//------------------------------------------------------------------------------
// slang_unifdef.cpp
// Standalone tool that simplifies selected `ifdef / `ifndef conditionals.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "SimplifyingPreprocessor.h"
#include <algorithm>
#include <cstdio>
#include <exception>
#include <filesystem>
#include <fstream>

#if defined(_WIN32)
#    include <fcntl.h>
#    include <io.h>
#endif

#include <fmt/format.h>
#include <optional>
#include <span>
#include <string>
#include <vector>

#include "slang/text/SourceLocation.h"
#include "slang/text/SourceManager.h"
#include "slang/util/CommandLine.h"
#include "slang/util/OS.h"
#include "slang/util/ThreadPool.h"
#include "slang/util/Util.h"

using namespace slang;

namespace {

class InputError : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};

struct RedactionResult {
    std::string output;
    std::exception_ptr exception;
};

bool isSourceFile(const std::filesystem::path& path) {
    auto ext = path.extension().string();
    return ext == ".sv" || ext == ".svh" || ext == ".v" || ext == ".vh";
}

std::vector<std::filesystem::path> collectInputs(std::span<const std::string> inputs) {
    std::vector<std::filesystem::path> paths;

    for (auto& input : inputs) {
        std::filesystem::path path(input);
        std::error_code ec;
        if (std::filesystem::is_directory(path, ec)) {
            for (auto it = std::filesystem::recursive_directory_iterator(path, ec);
                 !ec && it != std::filesystem::recursive_directory_iterator(); it.increment(ec)) {
                if (it->is_regular_file(ec) && isSourceFile(it->path()))
                    paths.push_back(it->path());
            }
            if (ec)
                SLANG_THROW(std::runtime_error(fmt::format("{}: {}", input, ec.message())));
        }
        else {
            paths.push_back(std::move(path));
        }
    }

    std::sort(paths.begin(), paths.end());
    return paths;
}

void writeFile(const std::filesystem::path& path, std::string_view text) {
    std::ofstream stream(path, std::ios::binary | std::ios::trunc);
    if (!stream)
        SLANG_THROW(
            std::runtime_error(fmt::format("{}: failed to open for writing", path.string())));

    stream.write(text.data(), std::streamsize(text.size()));
    if (!stream)
        SLANG_THROW(std::runtime_error(fmt::format("{}: failed to write output", path.string())));
}

RedactionResult redactPath(const std::filesystem::path& path,
                           std::span<const std::string> redactDefines,
                           std::span<const std::string> redactUndefines) {
    SourceManager sourceManager;
    auto buffer = sourceManager.readSource(path);
    if (!buffer)
        SLANG_THROW(InputError(fmt::format("{}: {}", path.string(), buffer.error().message())));

    SimplifyingPreprocessor preprocessor(sourceManager);
    for (auto& macro : redactDefines)
        preprocessor.setMacroValue(macro, true);
    for (auto& macro : redactUndefines)
        preprocessor.setMacroValue(macro, false);

    preprocessor.redact(*buffer);
    auto output = preprocessor.str();

    return {.output = std::move(output)};
}

std::vector<RedactionResult> redactPaths(const std::vector<std::filesystem::path>& paths,
                                         std::span<const std::string> redactDefines,
                                         std::span<const std::string> redactUndefines) {
    std::vector<RedactionResult> results(paths.size());

#if defined(SLANG_USE_THREADS)
    if (paths.size() > 1) {
        ThreadPool pool;
        auto futures = pool.submit_loop(size_t(0), paths.size(), [&](size_t i) {
            SLANG_TRY {
                results[i] = redactPath(paths[i], redactDefines, redactUndefines);
            }
            SLANG_CATCH(...) {
                results[i].exception = std::current_exception();
            }
        });
        futures.wait();
        return results;
    }
#endif

    for (size_t i = 0; i < paths.size(); i++)
        results[i] = redactPath(paths[i], redactDefines, redactUndefines);
    return results;
}

void rethrowFirstError(const std::vector<RedactionResult>& results) {
    for (auto& result : results) {
        if (result.exception)
            std::rethrow_exception(result.exception);
    }
}

} // namespace

int main(int argc, char** argv) {
    OS::setupConsole();

    SLANG_TRY {
        std::optional<bool> showHelp;
        std::optional<bool> inPlace;
        std::vector<std::string> redactDefines;
        std::vector<std::string> redactUndefines;
        std::vector<std::string> inputs;

        CommandLine cmdLine;

        cmdLine.add("-h,--help", showHelp, "Display available options");
        cmdLine.add("-i,--inplace", inPlace, "Rewrite input files in place");
        cmdLine.add("-D,--define", redactDefines,
                    "Simplify conditionals as if the named macro is defined", "<macro>",
                    CommandLineFlags::CommaList);
        cmdLine.add("-U,--undefine", redactUndefines,
                    "Simplify conditionals as if the named macro is undefined", "<macro>",
                    CommandLineFlags::CommaList);
        cmdLine.setPositional(inputs, "files-or-dirs");

        CommandLine::ParseOptions parseOptions;
        if (!cmdLine.parse(argc, argv, parseOptions)) {
            for (auto& error : cmdLine.getErrors())
                OS::printE(fmt::format("{}\n", error.message));
            return 1;
        }

        auto printHelp = [&]() {
            OS::print(
                fmt::format("{}", cmdLine.getHelpText("SystemVerilog conditional simplifier")));
        };

        if (showHelp == true) {
            printHelp();
            return 0;
        }

        auto paths = collectInputs(inputs);
        if (paths.empty()) {
            OS::printE("error: no input file specified\n");
            printHelp();
            return 1;
        }

        // Make sure we reproduce newlines correctly on Windows:
#if defined(_WIN32)
        _setmode(_fileno(stdout), _O_BINARY);
#endif

        auto results = redactPaths(paths, redactDefines, redactUndefines);
        rethrowFirstError(results);

        if (inPlace == true) {
            for (size_t i = 0; i < paths.size(); i++)
                writeFile(paths[i], results[i].output);
        }
        else {
            std::string stdoutOutput;
            for (auto& result : results)
                stdoutOutput.append(result.output);
            printf("%s", stdoutOutput.c_str());
        }
        return 0;
    }
    SLANG_CATCH(const InputError& e) {
        SLANG_REPORT_EXCEPTION(e, "{}\n");
        return 1;
    }
    SLANG_CATCH(const RedactionError& e) {
        SLANG_REPORT_EXCEPTION(e, "error: {}\n");
        return 1;
    }
    SLANG_CATCH(const std::exception& e) {
        SLANG_REPORT_EXCEPTION(e, "internal compiler error (exception): {}\n");
        return 2;
    }
}

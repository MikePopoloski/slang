//------------------------------------------------------------------------------
// UtilBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Symbol.h"
#include "slang/diagnostics/DiagnosticClient.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/parsing/Lexer.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceLocation.h"
#include "slang/text/SourceManager.h"
#include "slang/util/Bag.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/VersionInfo.h"

namespace fs = std::filesystem;

std::vector<nb::object> argConverter(const Diagnostic& self) {
    std::vector<nb::object> results;
    for (auto& argVar : self.args) {
        results.push_back(std::visit(
            [&](auto&& arg) {
                using T = std::decay_t<decltype(arg)>;
                if constexpr (std::is_same_v<T, Diagnostic::CustomArgType>)
                    return nb::cast(std::any_cast<const Type*>(arg.second), byrefint,
                                    nb::cast(&self));
                else
                    return nb::cast(arg);
            },
            argVar));
    }
    return results;
}

std::string argFormatter(const DiagnosticEngine& self, nb::object obj) {
    try {
        auto arg = nb::cast<const Type*>(obj);
        return self.formatArg(Diagnostic::CustomArgType{SLANG_TYPEOF(const Type*), arg});
    }
    catch (const nb::cast_error&) {
        auto arg = nb::cast<Diagnostic::Arg>(obj);
        return self.formatArg(arg);
    }
}

void registerText(nb::module_& m) {
    nb::enum_<SourceManager::BufferKind>(m, "BufferKind")
        .value("Unknown", SourceManager::BufferKind::Unknown)
        .value("DesignFile", SourceManager::BufferKind::DesignFile)
        .value("LibraryFile", SourceManager::BufferKind::LibraryFile)
        .value("LibraryMap", SourceManager::BufferKind::LibraryMap)
        .value("IncludeFile", SourceManager::BufferKind::IncludeFile)
        .value("Macro", SourceManager::BufferKind::Macro)
        .value("MacroArg", SourceManager::BufferKind::MacroArg);

    nb::class_<BufferID>(m, "BufferID")
        .def(nb::init<>())
        .def_prop_ro("id", &BufferID::getId)
        .def_static("getPlaceholder", &BufferID::getPlaceholder)
        .def_prop_ro_static("placeholder",
                            [](nb::object /* self or cls */) { return BufferID::getPlaceholder(); })
        .def(nb::self == nb::self)
        .def(nb::self != nb::self)
        .def(nb::self < nb::self)
        .def(nb::self <= nb::self)
        .def(nb::self > nb::self)
        .def(nb::self >= nb::self)
        .def(nb::hash(nb::self))
        .def("__bool__", &BufferID::valid)
        .def("__repr__",
             [](const BufferID& self) { return fmt::format("BufferID({})", self.getId()); });

    nb::class_<SourceLocation>(m, "SourceLocation")
        .def(nb::init<>())
        .def(nb::init<BufferID, size_t>(), "buffer"_a, "offset"_a)
        .def_prop_ro("buffer", &SourceLocation::buffer)
        .def_prop_ro("offset", &SourceLocation::offset)
        .def_ro_static("NoLocation", &SourceLocation::NoLocation)
        .def(nb::self == nb::self)
        .def(nb::self != nb::self)
        .def(nb::self < nb::self)
        .def(nb::self <= nb::self)
        .def(nb::self > nb::self)
        .def(nb::self >= nb::self)
        .def(nb::hash(nb::self))
        .def("__bool__", &SourceLocation::valid)
        .def("__repr__", [](const SourceLocation& self) {
            return fmt::format("SourceLocation({}, {})", self.buffer().getId(), self.offset());
        });

    nb::class_<SourceRange>(m, "SourceRange")
        .def(nb::init<>())
        .def(nb::init<SourceLocation, SourceLocation>(), "startLoc"_a, "endLoc"_a)
        .def_prop_ro("start", &SourceRange::start)
        .def_prop_ro("end", &SourceRange::end)
        .def(nb::self == nb::self)
        .def(nb::self != nb::self);

    nb::class_<SourceLibrary>(m, "SourceLibrary")
        .def(nb::init<>())
        .def_ro("name", &SourceLibrary::name);

    nb::class_<SourceBuffer>(m, "SourceBuffer")
        .def(nb::init<>())
        .def_ro("id", &SourceBuffer::id)
        .def_ro("library", &SourceBuffer::library, byrefint)
        .def_ro("data", &SourceBuffer::data)
        .def("__bool__", &SourceBuffer::operator bool);

    nb::class_<SourceManager>(m, "SourceManager")
        .def(nb::init<>())
        .def(
            "addSystemDirectories",
            [](SourceManager& self, std::string_view path) {
                auto ec = self.addSystemDirectories(path);
                if (ec)
                    throw fs::filesystem_error("", path, ec);
            },
            "path"_a)
        .def(
            "addUserDirectories",
            [](SourceManager& self, std::string_view path) {
                auto ec = self.addUserDirectories(path);
                if (ec)
                    throw fs::filesystem_error("", path, ec);
            },
            "path"_a)
        .def("getLineNumber", &SourceManager::getLineNumber, "location"_a)
        .def("getFileName", &SourceManager::getFileName, "location"_a)
        .def("getRawFileName", &SourceManager::getRawFileName, "buffer"_a)
        .def("getFullPath", &SourceManager::getFullPath, "buffer"_a)
        .def("getColumnNumber", &SourceManager::getColumnNumber, "location"_a)
        .def("getDisplayColumnNumber", &SourceManager::getDisplayColumnNumber, "location"_a)
        .def("getIncludedFrom", &SourceManager::getIncludedFrom, "buffer"_a)
        .def("getBufferKind", &SourceManager::getBufferKind, "buffer"_a)
        .def("setBufferKind", &SourceManager::setBufferKind, "buffer"_a, "kind"_a)
        .def("getMacroName", &SourceManager::getMacroName, "location"_a)
        .def("isFileLoc", &SourceManager::isFileLoc, "location"_a)
        .def("isMacroLoc", &SourceManager::isMacroLoc, "location"_a)
        .def("isMacroArgLoc", &SourceManager::isMacroArgLoc, "location"_a)
        .def("isIncludedFileLoc", &SourceManager::isIncludedFileLoc, "location"_a)
        .def("isPreprocessedLoc", &SourceManager::isPreprocessedLoc, "location"_a)
        .def("isBeforeInCompilationUnit", &SourceManager::isBeforeInCompilationUnit, "left"_a,
             "right"_a)
        .def("getExpansionLoc", &SourceManager::getExpansionLoc, "location"_a)
        .def("getExpansionRange", &SourceManager::getExpansionRange, "location"_a)
        .def("getOriginalLoc", &SourceManager::getOriginalLoc, "location"_a)
        .def("getFullyOriginalLoc", &SourceManager::getFullyOriginalLoc, "location"_a)
        .def("getFullyOriginalRange", &SourceManager::getFullyOriginalRange, "range"_a)
        .def("getFullyExpandedLoc", &SourceManager::getFullyExpandedLoc, "location"_a)
        .def("getSourceText", &SourceManager::getSourceText, "buffer"_a)
        .def("assignText",
             nb::overload_cast<std::string_view, SourceLocation, const SourceLibrary*>(
                 &SourceManager::assignText),
             "text"_a, "includedFrom"_a = SourceLocation(), "library"_a = nullptr)
        .def("assignText",
             nb::overload_cast<std::string_view, std::string_view, SourceLocation,
                               const SourceLibrary*>(&SourceManager::assignText),
             "path"_a, "text"_a, "includedFrom"_a = SourceLocation(), "library"_a = nullptr)
        .def(
            "readSource",
            [](SourceManager& self, const fs::path& path, const SourceLibrary* library) {
                auto result = self.readSource(path, library);
                if (!result)
                    throw fs::filesystem_error("", path, result.error());
                return *result;
            },
            "path"_a, "library"_a = nb::none())
        .def(
            "readHeader",
            [](SourceManager& self, std::string_view path, SourceLocation includedFrom,
               const SourceLibrary* library, bool isSystemPath) {
                auto result = self.readHeader(path, includedFrom, library, isSystemPath, {});
                if (!result)
                    throw fs::filesystem_error("", path, result.error());
                return *result;
            },
            "path"_a, "includedFrom"_a, "library"_a, "isSystemPath"_a)
        .def("isCached", &SourceManager::isCached, "path"_a)
        .def("setDisableProximatePaths", &SourceManager::setDisableProximatePaths, "set"_a)
        .def("setDisableLocalIncludes", &SourceManager::setDisableLocalIncludes, "set"_a)
        .def("addLineDirective", &SourceManager::addLineDirective, "location"_a, "lineNum"_a,
             "name"_a, "level"_a)
        .def("addDiagnosticDirective", &SourceManager::addDiagnosticDirective, "location"_a,
             "name"_a, "severity"_a)
        .def("getAllBuffers", &SourceManager::getAllBuffers);
}

void registerDiagnostics(nb::module_& m) {
    EXPOSE_ENUM(m, ColumnUnit);
    EXPOSE_ENUM(m, DiagSubsystem);
    EXPOSE_ENUM(m, DiagnosticSeverity);

    nb::class_<DiagCode>(m, "DiagCode")
        .def(nb::init<>())
        .def(nb::init<DiagSubsystem, uint16_t>(), "subsystem"_a, "code"_a)
        .def("getCode", &DiagCode::getCode)
        .def("getSubsystem", &DiagCode::getSubsystem)
        .def(nb::self == nb::self)
        .def(nb::self != nb::self)
        .def(nb::hash(nb::self))
        .def("__bool__", &DiagCode::valid)
        .def("__repr__",
             [](const DiagCode& self) { return fmt::format("DiagCode({})", toString(self)); });

    struct Diags {};
    nb::class_<Diags> diagHolder(m, "Diags");
    for (auto code : DiagCode::KnownCodes) {
        diagHolder.def_prop_ro_static(std::string(toString(code)).c_str(),
                                      [code](nb::object) { return code; });
    }

    nb::class_<Diagnostic>(m, "Diagnostic")
        .def(nb::init<DiagCode, SourceLocation>(), "code"_a, "location"_a)
        .def_ro("code", &Diagnostic::code)
        .def_ro("location", &Diagnostic::location)
        .def_ro("symbol", &Diagnostic::symbol)
        .def_ro("ranges", &Diagnostic::ranges)
        .def_prop_ro("args", &argConverter)
        .def("isError", &Diagnostic::isError)
        .def(nb::self == nb::self)
        .def(nb::self != nb::self);

    nb::class_<Diagnostics>(m, "Diagnostics")
        .def(nb::init<>())
        .def("add", nb::overload_cast<DiagCode, SourceLocation>(&Diagnostics::add), byrefint,
             "code"_a, "location"_a)
        .def("add", nb::overload_cast<DiagCode, SourceRange>(&Diagnostics::add), byrefint, "code"_a,
             "range"_a)
        .def("add", nb::overload_cast<const Symbol&, DiagCode, SourceLocation>(&Diagnostics::add),
             byrefint, "source"_a, "code"_a, "location"_a)
        .def("add", nb::overload_cast<const Symbol&, DiagCode, SourceRange>(&Diagnostics::add),
             byrefint, "source"_a, "code"_a, "range"_a)
        .def("sort", &Diagnostics::sort, "sourceManager"_a)
        .def("__len__", [](const Diagnostics& self) { return self.size(); })
        .def("__getitem__",
             [](const Diagnostics& s, size_t i) {
                 if (i >= s.size()) {
                     throw nb::index_error();
                 }
                 return s[i];
             })
        .def(
            "__iter__",
            [](const Diagnostics& self) {
                return nb::make_iterator(nb::type<Diagnostics>(), "DiagnosticsIterator",
                                         self.begin(), self.end());
            },
            nb::keep_alive<0, 1>());

    nb::class_<DiagGroup>(m, "DiagGroup")
        .def(nb::init<const std::string&, const std::vector<DiagCode>&>(), "name"_a, "diags"_a)
        .def("getName", &DiagGroup::getName)
        .def("getDiags", &DiagGroup::getDiags)
        .def("__repr__",
             [](const DiagGroup& self) { return fmt::format("DiagGroup({})", self.getName()); });

    nb::class_<DiagnosticEngine>(m, "DiagnosticEngine")
        .def(nb::init<const SourceManager&>(), nb::keep_alive<1, 2>(), "sourceManager"_a)
        .def("addClient", &DiagnosticEngine::addClient, "client"_a)
        .def("clearClients", &DiagnosticEngine::clearClients)
        .def("issue", nb::overload_cast<const Diagnostic&>(&DiagnosticEngine::issue),
             "diagnostic"_a)
        .def("issue", nb::overload_cast<const Diagnostics&>(&DiagnosticEngine::issue),
             "diagnostics"_a)
        .def_prop_ro("sourceManager", &DiagnosticEngine::getSourceManager)
        .def_prop_ro("numErrors", &DiagnosticEngine::getNumErrors)
        .def_prop_ro("numWarnings", &DiagnosticEngine::getNumWarnings)
        .def("clearCounts", &DiagnosticEngine::clearCounts)
        .def("setErrorLimit", &DiagnosticEngine::setErrorLimit, "limit"_a)
        .def("setIgnoreAllWarnings", &DiagnosticEngine::setIgnoreAllWarnings, "set"_a)
        .def("setIgnoreAllNotes", &DiagnosticEngine::setIgnoreAllNotes, "set"_a)
        .def("setWarningsAsErrors", &DiagnosticEngine::setWarningsAsErrors, "set"_a)
        .def("setErrorsAsFatal", &DiagnosticEngine::setErrorsAsFatal, "set"_a)
        .def("setFatalsAsErrors", &DiagnosticEngine::setFatalsAsErrors, "set"_a)
        .def("setSeverity", &DiagnosticEngine::setSeverity, "code"_a, "severity"_a)
        .def("setBaselineSeverity", &DiagnosticEngine::setBaselineSeverity, "code"_a, "severity"_a)
        .def("getSeverity", &DiagnosticEngine::getSeverity, "code"_a, "location"_a)
        .def("setMessage", &DiagnosticEngine::setMessage, "code"_a, "message"_a)
        .def("getMessage", &DiagnosticEngine::getMessage, "code"_a)
        .def("getOptionName", &DiagnosticEngine::getOptionName, "code"_a)
        .def("findFromOptionName", &DiagnosticEngine::findFromOptionName, "optionName"_a)
        .def("findDiagGroup", &DiagnosticEngine::findDiagGroup, byrefint, "name"_a)
        .def("clearMappings", nb::overload_cast<>(&DiagnosticEngine::clearMappings))
        .def("clearMappings",
             nb::overload_cast<DiagnosticSeverity>(&DiagnosticEngine::clearMappings), "severity"_a)
        .def("formatMessage", &DiagnosticEngine::formatMessage, "diag"_a)
        .def("setWarningOptions", &DiagnosticEngine::setWarningOptions, "options"_a)
        .def("setMappingsFromPragmas",
             nb::overload_cast<>(&DiagnosticEngine::setMappingsFromPragmas))
        .def("setMappingsFromPragmas",
             nb::overload_cast<BufferID>(&DiagnosticEngine::setMappingsFromPragmas), "buffer"_a)
        .def("formatArg", argFormatter)
        .def_static("reportAll", &DiagnosticEngine::reportAll, "sourceManager"_a, "diag"_a);

    nb::class_<ReportedDiagnostic>(m, "ReportedDiagnostic")
        .def_prop_ro("originalDiagnostic",
                     [](const ReportedDiagnostic& self) { return self.originalDiagnostic; })
        .def_ro("expansionLocs", &ReportedDiagnostic::expansionLocs)
        .def_ro("ranges", &ReportedDiagnostic::ranges)
        .def_ro("location", &ReportedDiagnostic::location)
        .def_ro("formattedMessage", &ReportedDiagnostic::formattedMessage)
        .def_ro("severity", &ReportedDiagnostic::severity)
        .def_ro("shouldShowIncludeStack", &ReportedDiagnostic::shouldShowIncludeStack);

    nb::class_<DiagnosticClient>(m, "DiagnosticClient")
        .def("report", &DiagnosticClient::report, "diagnostic"_a)
        .def("setEngine", &DiagnosticClient::setEngine, "engine"_a)
        .def("showAbsPaths", &DiagnosticClient::showAbsPaths, "show"_a);

    nb::class_<TextDiagnosticClient, DiagnosticClient>(m, "TextDiagnosticClient")
        .def(nb::init<>())
        .def("showColors", &TextDiagnosticClient::showColors, "show"_a)
        .def("showColumn", &TextDiagnosticClient::showColumn, "show"_a)
        .def("setColumnUnit", &TextDiagnosticClient::setColumnUnit, "unit"_a)
        .def("showLocation", &TextDiagnosticClient::showLocation, "show"_a)
        .def("showSourceLine", &TextDiagnosticClient::showSourceLine, "show"_a)
        .def("showOptionName", &TextDiagnosticClient::showOptionName, "show"_a)
        .def("showIncludeStack", &TextDiagnosticClient::showIncludeStack, "show"_a)
        .def("showMacroExpansion", &TextDiagnosticClient::showMacroExpansion, "show"_a)
        .def("showHierarchyInstance", &TextDiagnosticClient::showHierarchyInstance, "show"_a)
        .def("report", &TextDiagnosticClient::report, "diag"_a)
        .def("clear", &TextDiagnosticClient::clear)
        .def("getString", &TextDiagnosticClient::getString);
}

void registerUtil(nb::module_& m) {
    nb::class_<BumpAllocator>(m, "BumpAllocator").def(nb::init<>());

    nb::class_<Bag>(m, "Bag")
        .def(nb::init<>())
        .def(
            "__init__",
            [](Bag* self, nb::list list) {
                Bag result;
                for (auto item : list) {
                    auto type = item.type();
                    if (type.is(nb::type<LexerOptions>()))
                        result.set(nb::cast<LexerOptions>(item));
                    else if (type.is(nb::type<PreprocessorOptions>()))
                        result.set(nb::cast<PreprocessorOptions>(item));
                    else if (type.is(nb::type<ParserOptions>()))
                        result.set(nb::cast<ParserOptions>(item));
                    else if (type.is(nb::type<CompilationOptions>()))
                        result.set(nb::cast<CompilationOptions>(item));
                    else
                        throw nb::type_error();
                }
                new (self) Bag(std::move(result));
            },
            "list"_a)
        .def_prop_rw("lexerOptions", &Bag::get<LexerOptions>,
                     nb::overload_cast<const LexerOptions&>(&Bag::set<LexerOptions>))
        .def_prop_rw("preprocessorOptions", &Bag::get<PreprocessorOptions>,
                     nb::overload_cast<const PreprocessorOptions&>(&Bag::set<PreprocessorOptions>))
        .def_prop_rw("parserOptions", &Bag::get<ParserOptions>,
                     nb::overload_cast<const ParserOptions&>(&Bag::set<ParserOptions>))
        .def_prop_rw("compilationOptions", &Bag::get<CompilationOptions>,
                     nb::overload_cast<const CompilationOptions&>(&Bag::set<CompilationOptions>));

    nb::class_<VersionInfo>(m, "VersionInfo")
        .def_static("getMajor", &VersionInfo::getMajor)
        .def_static("getMinor", &VersionInfo::getMinor)
        .def_static("getPatch", &VersionInfo::getPatch)
        .def_static("getPrerelease", &VersionInfo::getPrerelease)
        .def_static("getHash", &VersionInfo::getHash)
        .def_static("getVersionString", &VersionInfo::getVersionString);
}

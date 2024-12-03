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

void registerUtil(py::module_& m) {
    py::class_<BumpAllocator>(m, "BumpAllocator").def(py::init<>());

    py::class_<Bag>(m, "Bag")
        .def(py::init<>())
        .def(py::init([](py::list list) {
                 Bag result;
                 for (auto item : list) {
                     auto type = py::type::of(item);
                     if (type.is(py::type::of<LexerOptions>()))
                         result.set(item.cast<LexerOptions>());
                     else if (type.is(py::type::of<PreprocessorOptions>()))
                         result.set(item.cast<PreprocessorOptions>());
                     else if (type.is(py::type::of<ParserOptions>()))
                         result.set(item.cast<ParserOptions>());
                     else if (type.is(py::type::of<CompilationOptions>()))
                         result.set(item.cast<CompilationOptions>());
                     else
                         throw py::type_error();
                 }
                 return result;
             }),
             "list"_a)
        .def_property("lexerOptions", &Bag::get<LexerOptions>,
                      py::overload_cast<const LexerOptions&>(&Bag::set<LexerOptions>))
        .def_property("preprocessorOptions", &Bag::get<PreprocessorOptions>,
                      py::overload_cast<const PreprocessorOptions&>(&Bag::set<PreprocessorOptions>))
        .def_property("parserOptions", &Bag::get<ParserOptions>,
                      py::overload_cast<const ParserOptions&>(&Bag::set<ParserOptions>))
        .def_property("compilationOptions", &Bag::get<CompilationOptions>,
                      py::overload_cast<const CompilationOptions&>(&Bag::set<CompilationOptions>));

    py::class_<BufferID>(m, "BufferID")
        .def(py::init<>())
        .def_property_readonly("id", &BufferID::getId)
        .def_static("getPlaceholder", &BufferID::getPlaceholder)
        .def_property_readonly_static(
            "placeholder", [](py::object /* self or cls */) { return BufferID::getPlaceholder(); })
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(py::hash(py::self))
        .def("__bool__", &BufferID::valid)
        .def("__repr__",
             [](const BufferID& self) { return fmt::format("BufferID({})", self.getId()); });

    py::class_<SourceLocation>(m, "SourceLocation")
        .def(py::init<>())
        .def(py::init<BufferID, size_t>(), "buffer"_a, "offset"_a)
        .def_property_readonly("buffer", &SourceLocation::buffer)
        .def_property_readonly("offset", &SourceLocation::offset)
        .def_readonly_static("NoLocation", &SourceLocation::NoLocation)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(py::hash(py::self))
        .def("__bool__", &SourceLocation::valid)
        .def("__repr__", [](const SourceLocation& self) {
            return fmt::format("SourceLocation({}, {})", self.buffer().getId(), self.offset());
        });

    py::class_<SourceRange>(m, "SourceRange")
        .def(py::init<>())
        .def(py::init<SourceLocation, SourceLocation>(), "startLoc"_a, "endLoc"_a)
        .def_property_readonly("start", &SourceRange::start)
        .def_property_readonly("end", &SourceRange::end)
        .def(py::self == py::self)
        .def(py::self != py::self);

    py::class_<SourceLibrary>(m, "SourceLibrary")
        .def(py::init<>())
        .def_readonly("name", &SourceLibrary::name);

    py::class_<SourceBuffer>(m, "SourceBuffer")
        .def(py::init<>())
        .def_readonly("id", &SourceBuffer::id)
        .def_readonly("library", &SourceBuffer::library, byrefint)
        .def_readonly("data", &SourceBuffer::data)
        .def("__bool__", &SourceBuffer::operator bool);

    py::class_<SourceManager>(m, "SourceManager")
        .def(py::init<>())
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
        .def("getIncludedFrom", &SourceManager::getIncludedFrom, "buffer"_a)
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
             py::overload_cast<std::string_view, SourceLocation, const SourceLibrary*>(
                 &SourceManager::assignText),
             "text"_a, "includedFrom"_a = SourceLocation(), "library"_a = nullptr)
        .def("assignText",
             py::overload_cast<std::string_view, std::string_view, SourceLocation,
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
            "path"_a, "library"_a = py::none())
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
        .def("addLineDirective", &SourceManager::addLineDirective, "location"_a, "lineNum"_a,
             "name"_a, "level"_a)
        .def("addDiagnosticDirective", &SourceManager::addDiagnosticDirective, "location"_a,
             "name"_a, "severity"_a)
        .def("getAllBuffers", &SourceManager::getAllBuffers);

    py::class_<VersionInfo>(m, "VersionInfo")
        .def_static("getMajor", &VersionInfo::getMajor)
        .def_static("getMinor", &VersionInfo::getMinor)
        .def_static("getPatch", &VersionInfo::getPatch)
        .def_static("getHash", &VersionInfo::getHash);

    EXPOSE_ENUM(m, DiagSubsystem);
    EXPOSE_ENUM(m, DiagnosticSeverity);

    py::class_<DiagCode>(m, "DiagCode")
        .def(py::init<>())
        .def(py::init<DiagSubsystem, uint16_t>(), "subsystem"_a, "code"_a)
        .def("getCode", &DiagCode::getCode)
        .def("getSubsystem", &DiagCode::getSubsystem)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::hash(py::self))
        .def("__bool__", &DiagCode::valid)
        .def("__repr__",
             [](const DiagCode& self) { return fmt::format("DiagCode({})", toString(self)); });

    struct Diags {};
    py::class_<Diags> diagHolder(m, "Diags");
    for (auto code : DiagCode::KnownCodes) {
        diagHolder.def_property_readonly_static(std::string(toString(code)).c_str(),
                                                [code](py::object) { return code; });
    }

    py::class_<Diagnostic>(m, "Diagnostic")
        .def(py::init<DiagCode, SourceLocation>(), "code"_a, "location"_a)
        .def_readonly("code", &Diagnostic::code)
        .def_readonly("location", &Diagnostic::location)
        .def_readonly("symbol", &Diagnostic::symbol)
        .def_readonly("args", &Diagnostic::args)
        .def_readonly("ranges", &Diagnostic::ranges)
        .def("isError", &Diagnostic::isError)
        .def(py::self == py::self)
        .def(py::self != py::self);

    py::class_<Diagnostics>(m, "Diagnostics")
        .def(py::init<>())
        .def("add", py::overload_cast<DiagCode, SourceLocation>(&Diagnostics::add), byrefint,
             "code"_a, "location"_a)
        .def("add", py::overload_cast<DiagCode, SourceRange>(&Diagnostics::add), byrefint, "code"_a,
             "range"_a)
        .def("add", py::overload_cast<const Symbol&, DiagCode, SourceLocation>(&Diagnostics::add),
             byrefint, "source"_a, "code"_a, "location"_a)
        .def("add", py::overload_cast<const Symbol&, DiagCode, SourceRange>(&Diagnostics::add),
             byrefint, "source"_a, "code"_a, "range"_a)
        .def("sort", &Diagnostics::sort, "sourceManager"_a)
        .def("__len__", [](const Diagnostics& self) { return self.size(); })
        .def("__getitem__",
             [](const Diagnostics& s, size_t i) {
                 if (i >= s.size()) {
                     throw py::index_error();
                 }
                 return s[i];
             })
        .def(
            "__iter__",
            [](const Diagnostics& self) { return py::make_iterator(self.begin(), self.end()); },
            py::keep_alive<0, 1>());

    py::class_<DiagGroup>(m, "DiagGroup")
        .def(py::init<const std::string&, const std::vector<DiagCode>&>(), "name"_a, "diags"_a)
        .def("getName", &DiagGroup::getName)
        .def("getDiags", &DiagGroup::getDiags)
        .def("__repr__",
             [](const DiagGroup& self) { return fmt::format("DiagGroup({})", self.getName()); });

    py::class_<DiagnosticEngine>(m, "DiagnosticEngine")
        .def(py::init<const SourceManager&>(), "sourceManager"_a)
        .def("addClient", &DiagnosticEngine::addClient, "client"_a)
        .def("clearClients", &DiagnosticEngine::clearClients)
        .def("issue", &DiagnosticEngine::issue, "diagnostic"_a)
        .def_property_readonly("sourceManager", &DiagnosticEngine::getSourceManager)
        .def_property_readonly("numErrors", &DiagnosticEngine::getNumErrors)
        .def_property_readonly("numWarnings", &DiagnosticEngine::getNumWarnings)
        .def("clearCounts", &DiagnosticEngine::clearCounts)
        .def("setErrorLimit", &DiagnosticEngine::setErrorLimit, "limit"_a)
        .def("setIgnoreAllWarnings", &DiagnosticEngine::setIgnoreAllWarnings, "set"_a)
        .def("setIgnoreAllNotes", &DiagnosticEngine::setIgnoreAllNotes, "set"_a)
        .def("setWarningsAsErrors", &DiagnosticEngine::setWarningsAsErrors, "set"_a)
        .def("setErrorsAsFatal", &DiagnosticEngine::setErrorsAsFatal, "set"_a)
        .def("setFatalsAsErrors", &DiagnosticEngine::setFatalsAsErrors, "set"_a)
        .def("setSeverity",
             py::overload_cast<DiagCode, DiagnosticSeverity>(&DiagnosticEngine::setSeverity),
             "code"_a, "severity"_a)
        .def("setSeverity",
             py::overload_cast<const DiagGroup&, DiagnosticSeverity>(
                 &DiagnosticEngine::setSeverity),
             "group"_a, "severity"_a)
        .def("getSeverity", &DiagnosticEngine::getSeverity, "code"_a, "location"_a)
        .def("setMessage", &DiagnosticEngine::setMessage, "code"_a, "message"_a)
        .def("getMessage", &DiagnosticEngine::getMessage, "code"_a)
        .def("getOptionName", &DiagnosticEngine::getOptionName, "code"_a)
        .def("findFromOptionName", &DiagnosticEngine::findFromOptionName, "optionName"_a)
        .def("findDiagGroup", &DiagnosticEngine::findDiagGroup, byrefint, "name"_a)
        .def("clearMappings", py::overload_cast<>(&DiagnosticEngine::clearMappings))
        .def("clearMappings",
             py::overload_cast<DiagnosticSeverity>(&DiagnosticEngine::clearMappings), "severity"_a)
        .def("formatMessage", &DiagnosticEngine::formatMessage, "diag"_a)
        .def("setDefaultWarnings", &DiagnosticEngine::setDefaultWarnings)
        .def("setWarningOptions", &DiagnosticEngine::setWarningOptions, "options"_a)
        .def("setMappingsFromPragmas",
             py::overload_cast<>(&DiagnosticEngine::setMappingsFromPragmas))
        .def("setMappingsFromPragmas",
             py::overload_cast<BufferID>(&DiagnosticEngine::setMappingsFromPragmas), "buffer"_a)
        .def_static("reportAll", &DiagnosticEngine::reportAll, "sourceManager"_a, "diag"_a);

    py::class_<ReportedDiagnostic>(m, "ReportedDiagnostic")
        .def_property_readonly("originalDiagnostic",
                               [](const ReportedDiagnostic& self) {
                                   return self.originalDiagnostic;
                               })
        .def_readonly("expansionLocs", &ReportedDiagnostic::expansionLocs)
        .def_readonly("ranges", &ReportedDiagnostic::ranges)
        .def_readonly("location", &ReportedDiagnostic::location)
        .def_readonly("formattedMessage", &ReportedDiagnostic::formattedMessage)
        .def_readonly("severity", &ReportedDiagnostic::severity)
        .def_readonly("shouldShowIncludeStack", &ReportedDiagnostic::shouldShowIncludeStack);

    py::class_<DiagnosticClient, std::shared_ptr<DiagnosticClient>>(m, "DiagnosticClient")
        .def("report", &DiagnosticClient::report, "diagnostic"_a)
        .def("setEngine", &DiagnosticClient::setEngine, "engine"_a);

    py::class_<TextDiagnosticClient, DiagnosticClient, std::shared_ptr<TextDiagnosticClient>>(
        m, "TextDiagnosticClient")
        .def(py::init<>())
        .def("showColors", &TextDiagnosticClient::showColors, "show"_a)
        .def("showColumn", &TextDiagnosticClient::showColumn, "show"_a)
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

//------------------------------------------------------------------------------
// util.cpp
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
#include "slang/util/Version.h"

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
        }))
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
        .def_property_readonly_static("placeholder", &BufferID::getPlaceholder)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(hash(py::self))
        .def("__bool__", &BufferID::valid)
        .def("__repr__",
             [](const BufferID& self) { return fmt::format("BufferID({})", self.getId()); });

    py::class_<SourceLocation>(m, "SourceLocation")
        .def(py::init<>())
        .def(py::init<BufferID, size_t>())
        .def_property_readonly("buffer", &SourceLocation::buffer)
        .def_property_readonly("offset", &SourceLocation::offset)
        .def_readonly_static("NoLocation", &SourceLocation::NoLocation)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(hash(py::self))
        .def("__bool__", &SourceLocation::valid)
        .def("__repr__", [](const SourceLocation& self) {
            return fmt::format("SourceLocation({}, {})", self.buffer().getId(), self.offset());
        });

    py::class_<SourceRange>(m, "SourceRange")
        .def(py::init<>())
        .def(py::init<SourceLocation, SourceLocation>())
        .def_property_readonly("start", &SourceRange::start)
        .def_property_readonly("end", &SourceRange::end)
        .def(py::self == py::self)
        .def(py::self != py::self);

    py::class_<SourceBuffer>(m, "SourceBuffer")
        .def(py::init<>())
        .def_readonly("id", &SourceBuffer::id)
        .def_readonly("data", &SourceBuffer::data)
        .def("__bool__", &SourceBuffer::operator bool);

    py::class_<SourceManager>(m, "SourceManager")
        .def(py::init<>())
        .def("makeAbsolutePath", &SourceManager::makeAbsolutePath, py::arg("path"))
        .def("addSystemDirectory", &SourceManager::addSystemDirectory, py::arg("path"))
        .def("addUserDirectory", &SourceManager::addUserDirectory, py::arg("path"))
        .def("getLineNumber", &SourceManager::getLineNumber, py::arg("location"))
        .def("getFileName", &SourceManager::getFileName, py::arg("location"))
        .def("getRawFileName", &SourceManager::getRawFileName, py::arg("buffer"))
        .def("getColumnNumber", &SourceManager::getColumnNumber, py::arg("location"))
        .def("getIncludedFrom", &SourceManager::getIncludedFrom, py::arg("buffer"))
        .def("getMacroName", &SourceManager::getMacroName, py::arg("location"))
        .def("isFileLoc", &SourceManager::isFileLoc, py::arg("location"))
        .def("isMacroLoc", &SourceManager::isMacroLoc, py::arg("location"))
        .def("isMacroArgLoc", &SourceManager::isMacroArgLoc, py::arg("location"))
        .def("isIncludedFileLoc", &SourceManager::isIncludedFileLoc, py::arg("location"))
        .def("isPreprocessedLoc", &SourceManager::isPreprocessedLoc, py::arg("location"))
        .def("isBeforeInCompilationUnit", &SourceManager::isBeforeInCompilationUnit,
             py::arg("left"), py::arg("right"))
        .def("getExpansionLoc", &SourceManager::getExpansionLoc, py::arg("location"))
        .def("getExpansionRange", &SourceManager::getExpansionRange, py::arg("location"))
        .def("getOriginalLoc", &SourceManager::getOriginalLoc, py::arg("location"))
        .def("getFullyOriginalLoc", &SourceManager::getFullyOriginalLoc, py::arg("location"))
        .def("getFullyExpandedLoc", &SourceManager::getFullyExpandedLoc, py::arg("location"))
        .def("getSourceText", &SourceManager::getSourceText, py::arg("buffer"))
        .def("assignText",
             py::overload_cast<string_view, SourceLocation>(&SourceManager::assignText), "text"_a,
             "includedFrom"_a = SourceLocation())
        .def("assignText",
             py::overload_cast<string_view, string_view, SourceLocation>(
                 &SourceManager::assignText),
             "path"_a, "text"_a, "includedFrom"_a = SourceLocation())
        .def("readSource", &SourceManager::readSource, py::arg("path"))
        .def("readHeader", &SourceManager::readHeader, py::arg("path"), py::arg("includedFrom"),
             py::arg("isSystemPath"))
        .def("isCached", &SourceManager::isCached, py::arg("path"))
        .def("setDisableProximatePaths", &SourceManager::setDisableProximatePaths, py::arg("set"))
        .def("addLineDirective", &SourceManager::addLineDirective, py::arg("location"),
             py::arg("lineNum"), py::arg("name"), py::arg("level"))
        .def("addDiagnosticDirective", &SourceManager::addDiagnosticDirective, py::arg("location"),
             py::arg("name"), py::arg("severity"))
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
        .def(py::init<DiagSubsystem, uint16_t>())
        .def("getCode", &DiagCode::getCode)
        .def("getSubsystem", &DiagCode::getSubsystem)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(hash(py::self))
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
        .def(py::init<DiagCode, SourceLocation>())
        .def_readonly("code", &Diagnostic::code)
        .def_readonly("location", &Diagnostic::location)
        .def_readonly("symbol", &Diagnostic::symbol)
        .def("isError", &Diagnostic::isError)
        .def(py::self == py::self)
        .def(py::self != py::self);

    py::class_<Diagnostics>(m, "Diagnostics")
        .def(py::init<>())
        .def("add", py::overload_cast<DiagCode, SourceLocation>(&Diagnostics::add), byrefint,
             py::arg("code"), py::arg("location"))
        .def("add", py::overload_cast<DiagCode, SourceRange>(&Diagnostics::add), byrefint,
             py::arg("code"), py::arg("range"))
        .def("add", py::overload_cast<const Symbol&, DiagCode, SourceLocation>(&Diagnostics::add),
             byrefint, py::arg("source"), py::arg("code"), py::arg("location"))
        .def("add", py::overload_cast<const Symbol&, DiagCode, SourceRange>(&Diagnostics::add),
             byrefint, py::arg("source"), py::arg("code"), py::arg("range"))
        .def("sort", &Diagnostics::sort, py::arg("sourceManager"))
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
        .def(py::init<const std::string&, const std::vector<DiagCode>&>())
        .def("getName", &DiagGroup::getName)
        .def("getDiags", &DiagGroup::getDiags)
        .def("__repr__",
             [](const DiagGroup& self) { return fmt::format("DiagGroup({})", self.getName()); });

    py::class_<DiagnosticEngine>(m, "DiagnosticEngine")
        .def(py::init<const SourceManager&>())
        .def("addClient", &DiagnosticEngine::addClient, py::arg("client"))
        .def("clearClients", &DiagnosticEngine::clearClients)
        .def("issue", &DiagnosticEngine::issue, py::arg("diagnostic"))
        .def_property_readonly("sourceManager", &DiagnosticEngine::getSourceManager)
        .def_property_readonly("numErrors", &DiagnosticEngine::getNumErrors)
        .def_property_readonly("numWarnings", &DiagnosticEngine::getNumWarnings)
        .def("clearCounts", &DiagnosticEngine::clearCounts)
        .def("setErrorLimit", &DiagnosticEngine::setErrorLimit, py::arg("limit"))
        .def("setIgnoreAllWarnings", &DiagnosticEngine::setIgnoreAllWarnings, py::arg("set"))
        .def("setIgnoreAllNotes", &DiagnosticEngine::setIgnoreAllNotes, py::arg("set"))
        .def("setWarningsAsErrors", &DiagnosticEngine::setWarningsAsErrors, py::arg("set"))
        .def("setErrorsAsFatal", &DiagnosticEngine::setErrorsAsFatal, py::arg("set"))
        .def("setFatalsAsErrors", &DiagnosticEngine::setFatalsAsErrors, py::arg("set"))
        .def("setSeverity",
             py::overload_cast<DiagCode, DiagnosticSeverity>(&DiagnosticEngine::setSeverity),
             py::arg("code"), py::arg("severity"))
        .def("setSeverity",
             py::overload_cast<const DiagGroup&, DiagnosticSeverity>(
                 &DiagnosticEngine::setSeverity),
             py::arg("group"), py::arg("severity"))
        .def("getSeverity", &DiagnosticEngine::getSeverity, py::arg("code"), py::arg("location"))
        .def("setMessage", &DiagnosticEngine::setMessage, py::arg("code"), py::arg("message"))
        .def("getMessage", &DiagnosticEngine::getMessage, py::arg("code"))
        .def("getOptionName", &DiagnosticEngine::getOptionName, py::arg("code"))
        .def("findFromOptionName", &DiagnosticEngine::findFromOptionName, py::arg("optionName"))
        .def("findDiagGroup", &DiagnosticEngine::findDiagGroup, byrefint, py::arg("name"))
        .def("clearMappings", py::overload_cast<>(&DiagnosticEngine::clearMappings))
        .def("clearMappings",
             py::overload_cast<DiagnosticSeverity>(&DiagnosticEngine::clearMappings),
             py::arg("severity"))
        .def("formatMessage", &DiagnosticEngine::formatMessage, py::arg("diag"))
        .def("setDefaultWarnings", &DiagnosticEngine::setDefaultWarnings)
        .def("setWarningOptions", &DiagnosticEngine::setWarningOptions, py::arg("options"))
        .def("setMappingsFromPragmas",
             py::overload_cast<>(&DiagnosticEngine::setMappingsFromPragmas))
        .def("setMappingsFromPragmas",
             py::overload_cast<BufferID>(&DiagnosticEngine::setMappingsFromPragmas),
             py::arg("buffer"))
        .def_static("reportAll", &DiagnosticEngine::reportAll, py::arg("sourceManager"),
                    py::arg("diag"));

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
        .def("report", &DiagnosticClient::report, py::arg("diagnostic"))
        .def("setEngine", &DiagnosticClient::setEngine, py::arg("engine"));

    py::class_<TextDiagnosticClient, DiagnosticClient, std::shared_ptr<TextDiagnosticClient>>(
        m, "TextDiagnosticClient")
        .def(py::init<>())
        .def("showColors", &TextDiagnosticClient::showColors, py::arg("show"))
        .def("showColumn", &TextDiagnosticClient::showColumn, py::arg("show"))
        .def("showLocation", &TextDiagnosticClient::showLocation, py::arg("show"))
        .def("showSourceLine", &TextDiagnosticClient::showSourceLine, py::arg("show"))
        .def("showOptionName", &TextDiagnosticClient::showOptionName, py::arg("show"))
        .def("showIncludeStack", &TextDiagnosticClient::showIncludeStack, py::arg("show"))
        .def("showMacroExpansion", &TextDiagnosticClient::showMacroExpansion, py::arg("show"))
        .def("showHierarchyInstance", &TextDiagnosticClient::showHierarchyInstance, py::arg("show"))
        .def("report", &TextDiagnosticClient::report, py::arg("diag"))
        .def("clear", &TextDiagnosticClient::clear)
        .def("getString", &TextDiagnosticClient::getString);
}

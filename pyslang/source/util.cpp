//------------------------------------------------------------------------------
// util.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/diagnostics/Diagnostics.h"
#include "slang/text/SourceLocation.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/Version.h"

void registerUtil(py::module_& m) {
    py::class_<BumpAllocator>(m, "BumpAllocator").def(py::init<>());

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
        .def("__bool__", &SourceBuffer::operator bool);

    py::class_<SourceManager>(m, "SourceManager")
        .def(py::init<>())
        .def("makeAbsolutePath", &SourceManager::makeAbsolutePath)
        .def("addSystemDirectory", &SourceManager::addSystemDirectory)
        .def("addUserDirectory", &SourceManager::addUserDirectory)
        .def("getLineNumber", &SourceManager::getLineNumber)
        .def("getFileName", &SourceManager::getFileName)
        .def("getRawFileName", &SourceManager::getRawFileName)
        .def("getColumnNumber", &SourceManager::getColumnNumber)
        .def("getIncludedFrom", &SourceManager::getIncludedFrom)
        .def("getMacroName", &SourceManager::getMacroName)
        .def("isFileLoc", &SourceManager::isFileLoc)
        .def("isMacroLoc", &SourceManager::isMacroLoc)
        .def("isMacroArgLoc", &SourceManager::isMacroArgLoc)
        .def("isIncludedFileLoc", &SourceManager::isIncludedFileLoc)
        .def("isPreprocessedLoc", &SourceManager::isPreprocessedLoc)
        .def("isBeforeInCompilationUnit", &SourceManager::isBeforeInCompilationUnit)
        .def("getExpansionLoc", &SourceManager::getExpansionLoc)
        .def("getExpansionRange", &SourceManager::getExpansionRange)
        .def("getOriginalLoc", &SourceManager::getOriginalLoc)
        .def("getFullyOriginalLoc", &SourceManager::getFullyOriginalLoc)
        .def("getFullyExpandedLoc", &SourceManager::getFullyExpandedLoc)
        .def("getSourceText", &SourceManager::getSourceText)
        .def("assignText",
             py::overload_cast<string_view, SourceLocation>(&SourceManager::assignText), "text"_a,
             "includedFrom"_a = SourceLocation())
        .def(
            "assignText",
            py::overload_cast<string_view, string_view, SourceLocation>(&SourceManager::assignText),
            "path"_a, "text"_a, "includedFrom"_a = SourceLocation())
        .def("readSource", &SourceManager::readSource)
        .def("readHeader", &SourceManager::readHeader)
        .def("isCached", &SourceManager::isCached)
        .def("setDisableProximatePaths", &SourceManager::setDisableProximatePaths)
        .def("addLineDirective", &SourceManager::addLineDirective)
        .def("addDiagnosticDirective", &SourceManager::addDiagnosticDirective);

    py::class_<VersionInfo>(m, "VersionInfo")
        .def_static("getMajor", &VersionInfo::getMajor)
        .def_static("getMinor", &VersionInfo::getMinor)
        .def_static("getRevision", &VersionInfo::getRevision);

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
}

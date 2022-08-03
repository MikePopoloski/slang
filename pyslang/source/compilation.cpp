//------------------------------------------------------------------------------
// compilation.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/compilation/Compilation.h"

#include "pyslang.h"

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/ScriptSession.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/types/NetType.h"

void registerCompilation(py::module_& m) {
    py::enum_<MinTypMax>(m, "MinTypMax")
        .value("Min", MinTypMax::Min)
        .value("Typ", MinTypMax::Typ)
        .value("Max", MinTypMax::Max);

    py::class_<CompilationOptions>(m, "CompilationOptions")
        .def(py::init<>())
        .def_readwrite("maxInstanceDepth", &CompilationOptions::maxInstanceDepth)
        .def_readwrite("maxGenerateSteps", &CompilationOptions::maxGenerateSteps)
        .def_readwrite("maxConstexprDepth", &CompilationOptions::maxConstexprDepth)
        .def_readwrite("maxConstexprSteps", &CompilationOptions::maxConstexprSteps)
        .def_readwrite("maxConstexprBacktrace", &CompilationOptions::maxConstexprBacktrace)
        .def_readwrite("maxDefParamSteps", &CompilationOptions::maxDefParamSteps)
        .def_readwrite("errorLimit", &CompilationOptions::errorLimit)
        .def_readwrite("typoCorrectionLimit", &CompilationOptions::typoCorrectionLimit)
        .def_readwrite("minTypMax", &CompilationOptions::minTypMax)
        .def_readwrite("allowHierarchicalConst", &CompilationOptions::allowHierarchicalConst)
        .def_readwrite("relaxEnumConversions", &CompilationOptions::relaxEnumConversions)
        .def_readwrite("allowDupInitialDrivers", &CompilationOptions::allowDupInitialDrivers)
        .def_readwrite("strictDriverChecking", &CompilationOptions::strictDriverChecking)
        .def_readwrite("lintMode", &CompilationOptions::lintMode)
        .def_readwrite("suppressUnused", &CompilationOptions::suppressUnused)
        .def_readwrite("topModules", &CompilationOptions::topModules)
        .def_readwrite("paramOverrides", &CompilationOptions::paramOverrides);

    py::class_<Compilation>(m, "Compilation")
        .def(py::init<>())
        .def(py::init<const Bag&>())
        .def_property_readonly("options", &Compilation::getOptions)
        .def_property_readonly("isFinalized", &Compilation::isFinalized)
        .def_property_readonly("sourceManager", &Compilation::getSourceManager)
        .def("addSyntaxTree", &Compilation::addSyntaxTree)
        .def("getSyntaxTrees", &Compilation::getSyntaxTrees)
        .def("getRoot", py::overload_cast<>(&Compilation::getRoot), byrefint)
        //.def("addSystemSubroutine", &Compilation::addSystemSubroutine)
        //.def("addSystemMethod", &Compilation::addSystemMethod)
        .def("getSystemSubroutine", &Compilation::getSystemSubroutine, byrefint)
        .def("getSystemMethod", &Compilation::getSystemMethod, byrefint)
        .def("parseName", &Compilation::parseName, byrefint)
        .def("tryParseName", &Compilation::tryParseName, byrefint)
        .def("createScriptScope", &Compilation::createScriptScope, byrefint)
        .def("getParseDiagnostics", &Compilation::getParseDiagnostics, byrefint)
        .def("getSemanticDiagnostics", &Compilation::getSemanticDiagnostics, byrefint)
        .def("getAllDiagnostics", &Compilation::getAllDiagnostics, byrefint)
        .def("addDiagnostics", &Compilation::addDiagnostics)
        .def_property("defaultTimeScale", &Compilation::getDefaultTimeScale,
                      &Compilation::setDefaultTimeScale)
        .def("getType", py::overload_cast<SyntaxKind>(&Compilation::getType, py::const_), byrefint)
        .def("getNetType", &Compilation::getNetType, byrefint)
        .def_property_readonly("bitType", &Compilation::getBitType)
        .def_property_readonly("logicType", &Compilation::getLogicType)
        .def_property_readonly("intType", &Compilation::getIntType)
        .def_property_readonly("byteType", &Compilation::getByteType)
        .def_property_readonly("integerType", &Compilation::getIntegerType)
        .def_property_readonly("realType", &Compilation::getRealType)
        .def_property_readonly("shortRealType", &Compilation::getShortRealType)
        .def_property_readonly("stringType", &Compilation::getStringType)
        .def_property_readonly("voidType", &Compilation::getVoidType)
        .def_property_readonly("errorType", &Compilation::getErrorType)
        .def_property_readonly("unsignedIntType", &Compilation::getUnsignedIntType)
        .def_property_readonly("nullType", &Compilation::getNullType)
        .def_property_readonly("unboundedType", &Compilation::getUnboundedType)
        .def_property_readonly("typeRefType", &Compilation::getTypeRefType)
        .def_property_readonly("wireNetType", &Compilation::getWireNetType);

    py::class_<ScriptSession>(m, "ScriptSession")
        .def(py::init<>())
        .def_readonly("compilation", &ScriptSession::compilation)
        .def("eval", &ScriptSession::eval)
        .def("evalExpression", &ScriptSession::evalExpression)
        .def("evalStatement", &ScriptSession::evalStatement)
        .def("getDiagnostics", &ScriptSession::getDiagnostics);
}

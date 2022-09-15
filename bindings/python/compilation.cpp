//------------------------------------------------------------------------------
// compilation.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"

#include "pyslang.h"

#include "slang/ast/Definition.h"
#include "slang/ast/ScriptSession.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

using namespace slang::driver;

void registerCompilation(py::module_& m) {
    EXPOSE_ENUM(m, VariableLifetime);
    EXPOSE_ENUM(m, Visibility);
    EXPOSE_ENUM(m, ArgumentDirection);
    EXPOSE_ENUM(m, ProceduralBlockKind);
    EXPOSE_ENUM(m, StatementBlockKind);
    EXPOSE_ENUM(m, DefinitionKind);
    EXPOSE_ENUM(m, UnconnectedDrive);
    EXPOSE_ENUM(m, EdgeKind);
    EXPOSE_ENUM(m, SubroutineKind);
    EXPOSE_ENUM(m, AssertionKind);
    EXPOSE_ENUM(m, ElabSystemTaskKind);
    EXPOSE_ENUM(m, RandMode);
    EXPOSE_ENUM(m, PrimitivePortDirection);
    EXPOSE_ENUM(m, DriverKind);

    py::class_<Definition>(m, "Definition")
        .def_readonly("name", &Definition::name)
        .def_readonly("location", &Definition::location)
        .def_readonly("definitionKind", &Definition::definitionKind)
        .def_readonly("defaultLifetime", &Definition::defaultLifetime)
        .def_readonly("unconnectedDrive", &Definition::unconnectedDrive)
        .def_readonly("timeScale", &Definition::timeScale)
        .def_readonly("attributes", &Definition::attributes)
        .def_property_readonly("syntax", [](const Definition& self) { return &self.syntax; })
        .def_property_readonly("defaultNetType",
                               [](const Definition& self) { return &self.defaultNetType; })
        .def_property_readonly("scope", [](const Definition& self) { return &self.scope; })
        .def_property_readonly("hierarchicalPath",
                               [](const Definition& self) {
                                   std::string str;
                                   self.getHierarchicalPath(str);
                                   return str;
                               })
        .def_property_readonly("isInstantiated", &Definition::isInstantiated)
        .def("getKindString", &Definition::getKindString)
        .def("getArticleKindString", &Definition::getArticleKindString)
        .def("__repr__",
             [](const Definition& self) { return fmt::format("Definition(\"{}\")", self.name); });

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
        .def("addSystemSubroutine",
             py::overload_cast<const SystemSubroutine&>(&Compilation::addSystemSubroutine),
             py::keep_alive<1, 2>())
        .def("addSystemMethod",
             py::overload_cast<SymbolKind, const SystemSubroutine&>(&Compilation::addSystemMethod),
             py::keep_alive<1, 3>())
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

    py::class_<Driver>(m, "Driver")
        .def(py::init<>())
        .def_readonly("sourceManager", &Driver::sourceManager)
        .def_readonly("diagEngine", &Driver::diagEngine)
        .def_readonly("diagClient", &Driver::diagClient)
        .def_readonly("buffers", &Driver::buffers)
        .def_readonly("syntaxTrees", &Driver::syntaxTrees)
        .def("addStandardArgs", &Driver::addStandardArgs)
        .def("parseCommandLine",
             [](Driver& self, string_view arg) { return self.parseCommandLine(arg); })
        .def("readSource", &Driver::readSource)
        .def("processCommandFile", &Driver::processCommandFile)
        .def("processOptions", &Driver::processOptions)
        .def("runPreprocessor", &Driver::runPreprocessor)
        .def("reportMacros", &Driver::reportMacros)
        .def("parseAllSources", &Driver::parseAllSources)
        .def("createOptionBag", &Driver::createOptionBag)
        .def("createCompilation", &Driver::createCompilation)
        .def("reportParseDiags", &Driver::reportParseDiags)
        .def("reportCompilation", &Driver::reportCompilation);

    class PySystemSubroutine : public SystemSubroutine {
    public:
        PySystemSubroutine(const std::string& name, SubroutineKind kind) :
            SystemSubroutine(name, kind) {}

        bool allowEmptyArgument(size_t argIndex) const override {
            PYBIND11_OVERRIDE(bool, SystemSubroutine, allowEmptyArgument, argIndex);
        }

        bool allowClockingArgument(size_t argIndex) const override {
            PYBIND11_OVERRIDE(bool, SystemSubroutine, allowClockingArgument, argIndex);
        }

        const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                       const ExpressionSyntax& syntax,
                                       const Args& previousArgs) const override {
            PYBIND11_OVERRIDE(const Expression&, SystemSubroutine, bindArgument, argIndex, context,
                              syntax, previousArgs);
        }

        const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                                   const Expression* iterOrThis) const override {
            PYBIND11_OVERRIDE_PURE(const Type&, SystemSubroutine, checkArguments, &context, args,
                                   range, iterOrThis);
        }

        ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                           const CallExpression::SystemCallInfo& callInfo) const override {
            PYBIND11_OVERRIDE_PURE(ConstantValue, SystemSubroutine, eval, &context, args, range,
                                   callInfo);
        }
    };

    class SystemSubroutinePublicist : public SystemSubroutine {
    public:
        using SystemSubroutine::badArg;
        using SystemSubroutine::checkArgCount;
        using SystemSubroutine::kindStr;
        using SystemSubroutine::noHierarchical;
        using SystemSubroutine::notConst;
        using SystemSubroutine::SystemSubroutine;
        using SystemSubroutine::unevaluatedContext;
    };

    py::class_<SystemSubroutine, PySystemSubroutine> systemSub(m, "SystemSubroutine");
    systemSub.def(py::init_alias<const std::string&, SubroutineKind>())
        .def_readwrite("name", &SystemSubroutine::name)
        .def_readwrite("kind", &SystemSubroutine::kind)
        .def_readwrite("hasOutputArgs", &SystemSubroutine::hasOutputArgs)
        .def_readwrite("withClauseMode", &SystemSubroutine::withClauseMode)
        .def("allowEmptyArgument", &SystemSubroutine::allowEmptyArgument)
        .def("allowClockingArgument", &SystemSubroutine::allowClockingArgument)
        .def("bindArgument", &SystemSubroutine::bindArgument)
        .def("checkArguments", &SystemSubroutine::checkArguments)
        .def("eval", &SystemSubroutine::eval)
        .def("badArg", &SystemSubroutinePublicist::badArg)
        .def("checkArgCount", &SystemSubroutinePublicist::checkArgCount)
        .def("kindStr", &SystemSubroutinePublicist::kindStr)
        .def("noHierarchical", &SystemSubroutinePublicist::noHierarchical)
        .def("notConst", &SystemSubroutinePublicist::notConst)
        .def("unevaluatedContext", &SystemSubroutinePublicist::unevaluatedContext)
        .def("__repr__", [](const SystemSubroutine& self) { return self.name; });

    py::enum_<SystemSubroutine::WithClauseMode>(systemSub, "WithClauseMode")
        .value("None", SystemSubroutine::WithClauseMode::None)
        .value("Iterator", SystemSubroutine::WithClauseMode::Iterator)
        .value("Randomize", SystemSubroutine::WithClauseMode::Randomize);

    class PySimpleSystemSubroutine : public SimpleSystemSubroutine {
    public:
        PySimpleSystemSubroutine(const std::string& name, SubroutineKind kind, size_t requiredArgs,
                                 const std::vector<const Type*>& argTypes, const Type& returnType,
                                 bool isMethod, bool isFirstArgLValue = false) :
            SimpleSystemSubroutine(name, kind, requiredArgs, argTypes, returnType, isMethod,
                                   isFirstArgLValue) {}

        ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                           const CallExpression::SystemCallInfo& callInfo) const override {
            PYBIND11_OVERRIDE_PURE(ConstantValue, SimpleSystemSubroutine, eval, &context, args,
                                   range, callInfo);
        }
    };

    py::class_<SimpleSystemSubroutine, SystemSubroutine, PySimpleSystemSubroutine>(
        m, "SimpleSystemSubroutine")
        .def(py::init_alias<const std::string&, SubroutineKind, size_t,
                            const std::vector<const Type*>&, const Type&, bool, bool>());

    py::class_<NonConstantFunction, SimpleSystemSubroutine>(m, "NonConstantFunction")
        .def(py::init<const std::string&, const Type&, size_t, const std::vector<const Type*>&,
                      bool>(),
             "name"_a, "returnType"_a, "requiredArgs"_a = 0,
             "argTypes"_a = std::vector<const Type*>{}, "isMethod"_a = false);
}

//------------------------------------------------------------------------------
// CompBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/ast/Compilation.h"
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

    py::enum_<MinTypMax>(m, "MinTypMax")
        .value("Min", MinTypMax::Min)
        .value("Typ", MinTypMax::Typ)
        .value("Max", MinTypMax::Max);

    py::enum_<CompilationFlags>(m, "CompilationFlags")
        .value("None_", CompilationFlags::None)
        .value("AllowHierarchicalConst", CompilationFlags::AllowHierarchicalConst)
        .value("RelaxEnumConversions", CompilationFlags::RelaxEnumConversions)
        .value("AllowUseBeforeDeclare", CompilationFlags::AllowUseBeforeDeclare)
        .value("AllowDupInitialDrivers", CompilationFlags::AllowDupInitialDrivers)
        .value("AllowTopLevelIfacePorts", CompilationFlags::AllowTopLevelIfacePorts)
        .value("StrictDriverChecking", CompilationFlags::StrictDriverChecking)
        .value("LintMode", CompilationFlags::LintMode)
        .value("SuppressUnused", CompilationFlags::SuppressUnused)
        .value("IgnoreUnknownModules", CompilationFlags::IgnoreUnknownModules)
        .value("RelaxStringConversions", CompilationFlags::RelaxStringConversions)
        .value("AllowRecursiveImplicitCall", CompilationFlags::AllowRecursiveImplicitCall)
        .value("AllowBareValParamAssignment", CompilationFlags::AllowBareValParamAssignment)
        .value("AllowSelfDeterminedStreamConcat", CompilationFlags::AllowSelfDeterminedStreamConcat)
        .value("AllowMultiDrivenLocals", CompilationFlags::AllowMultiDrivenLocals)
        .value("AllowMergingAnsiPorts", CompilationFlags::AllowMergingAnsiPorts);

    py::class_<CompilationOptions>(m, "CompilationOptions")
        .def(py::init<>())
        .def_readwrite("flags", &CompilationOptions::flags)
        .def_readwrite("maxInstanceDepth", &CompilationOptions::maxInstanceDepth)
        .def_readwrite("maxGenerateSteps", &CompilationOptions::maxGenerateSteps)
        .def_readwrite("maxConstexprDepth", &CompilationOptions::maxConstexprDepth)
        .def_readwrite("maxConstexprSteps", &CompilationOptions::maxConstexprSteps)
        .def_readwrite("maxConstexprBacktrace", &CompilationOptions::maxConstexprBacktrace)
        .def_readwrite("maxDefParamSteps", &CompilationOptions::maxDefParamSteps)
        .def_readwrite("maxInstanceArray", &CompilationOptions::maxInstanceArray)
        .def_readwrite("errorLimit", &CompilationOptions::errorLimit)
        .def_readwrite("typoCorrectionLimit", &CompilationOptions::typoCorrectionLimit)
        .def_readwrite("minTypMax", &CompilationOptions::minTypMax)
        .def_readwrite("languageVersion", &CompilationOptions::languageVersion)
        .def_readwrite("defaultTimeScale", &CompilationOptions::defaultTimeScale)
        .def_readwrite("topModules", &CompilationOptions::topModules)
        .def_readwrite("paramOverrides", &CompilationOptions::paramOverrides)
        .def_readwrite("defaultLiblist", &CompilationOptions::defaultLiblist);

    py::class_<Compilation> comp(m, "Compilation");
    comp.def(py::init<>())
        .def(py::init<const Bag&>(), "options"_a)
        .def_property_readonly("options", &Compilation::getOptions)
        .def_property_readonly("isFinalized", &Compilation::isFinalized)
        .def_property_readonly("sourceManager", &Compilation::getSourceManager)
        .def_property_readonly("defaultLibrary", &Compilation::getDefaultLibrary)
        .def("addSyntaxTree", &Compilation::addSyntaxTree, "tree"_a)
        .def("getSyntaxTrees", &Compilation::getSyntaxTrees)
        .def("getRoot", py::overload_cast<>(&Compilation::getRoot), byrefint)
        .def("addSystemSubroutine", &Compilation::addSystemSubroutine, py::keep_alive<1, 2>(),
             "subroutine"_a)
        .def("addSystemMethod", &Compilation::addSystemMethod, py::keep_alive<1, 3>(), "typeKind"_a,
             "method"_a)
        .def("getSystemSubroutine", &Compilation::getSystemSubroutine, byrefint, "name"_a)
        .def("getSystemMethod", &Compilation::getSystemMethod, byrefint, "typeKind"_a, "name"_a)
        .def("parseName", &Compilation::parseName, byrefint, "name"_a)
        .def("tryParseName", &Compilation::tryParseName, byrefint, "name"_a, "diags"_a)
        .def("createScriptScope", &Compilation::createScriptScope, byrefint)
        .def("getParseDiagnostics", &Compilation::getParseDiagnostics, byrefint)
        .def("getSemanticDiagnostics", &Compilation::getSemanticDiagnostics, byrefint)
        .def("getAllDiagnostics", &Compilation::getAllDiagnostics, byrefint)
        .def("addDiagnostics", &Compilation::addDiagnostics, "diagnostics"_a)
        .def("getCompilationUnit", &Compilation::getCompilationUnit, byrefint, "syntax"_a)
        .def("getCompilationUnits", &Compilation::getCompilationUnits, byrefint)
        .def("getSourceLibrary", &Compilation::getSourceLibrary, byrefint, "name"_a)
        .def("tryGetDefinition", &Compilation::tryGetDefinition, byrefint, "name"_a, "scope"_a)
        .def("getDefinitions", &Compilation::getDefinitions, byrefint)
        .def("getPackage", &Compilation::getPackage, byrefint, "name"_a)
        .def("getStdPackage", &Compilation::getStdPackage, byrefint)
        .def("getPackages", &Compilation::getPackages, byrefint)
        .def("getGateType", &Compilation::getGateType, byrefint, "name"_a)
        .def("getAttributes",
             py::overload_cast<const Symbol&>(&Compilation::getAttributes, py::const_), byrefint,
             "symbol"_a)
        .def("getAttributes",
             py::overload_cast<const Statement&>(&Compilation::getAttributes, py::const_), byrefint,
             "stmt"_a)
        .def("getAttributes",
             py::overload_cast<const Expression&>(&Compilation::getAttributes, py::const_),
             byrefint, "expr"_a)
        .def("getAttributes",
             py::overload_cast<const PortConnection&>(&Compilation::getAttributes, py::const_),
             byrefint, "conn"_a)
        .def("getType", py::overload_cast<SyntaxKind>(&Compilation::getType, py::const_), byrefint,
             "kind"_a)
        .def("getNetType", &Compilation::getNetType, byrefint, "kind"_a)
        .def_property_readonly("defaultTimeScale", &Compilation::getDefaultTimeScale)
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
        .def_property_readonly("wireNetType", &Compilation::getWireNetType)
        .def_property_readonly("hasIssuedErrors", &Compilation::hasIssuedErrors);

    py::class_<Compilation::DefinitionLookupResult>(comp, "DefinitionLookupResult")
        .def(py::init<>())
        .def_readwrite("definition", &Compilation::DefinitionLookupResult::definition)
        .def_readwrite("configRoot", &Compilation::DefinitionLookupResult::configRoot)
        .def_readwrite("configRule", &Compilation::DefinitionLookupResult::configRule);

    py::class_<ScriptSession>(m, "ScriptSession")
        .def(py::init<>())
        .def_readonly("compilation", &ScriptSession::compilation)
        .def("eval", &ScriptSession::eval, "text"_a)
        .def("evalExpression", &ScriptSession::evalExpression, "expr"_a)
        .def("evalStatement", &ScriptSession::evalStatement, "expr"_a)
        .def("getDiagnostics", &ScriptSession::getDiagnostics);

    py::class_<CommandLine::ParseOptions>(m, "CommandLineOptions")
        .def(py::init<>())
        .def_readwrite("supportsComments", &CommandLine::ParseOptions::supportComments)
        .def_readwrite("ignoreProgramName", &CommandLine::ParseOptions::ignoreProgramName)
        .def_readwrite("expandEnvVars", &CommandLine::ParseOptions::expandEnvVars)
        .def_readwrite("ignoreDuplicates", &CommandLine::ParseOptions::ignoreDuplicates);

    py::enum_<LanguageVersion>(m, "LanguageVersion")
        .value("v1800_2017", LanguageVersion::v1800_2017)
        .value("v1800_2023", LanguageVersion::v1800_2023)
        .value("Default", LanguageVersion::Default);

    py::class_<Driver>(m, "Driver")
        .def(py::init<>())
        .def_readonly("sourceManager", &Driver::sourceManager)
        .def_readonly("diagEngine", &Driver::diagEngine)
        .def_readonly("textDiagClient", &Driver::textDiagClient)
        .def_readonly("sourceLoader", &Driver::sourceLoader)
        .def_readonly("syntaxTrees", &Driver::syntaxTrees)
        .def_readwrite("languageVersion", &Driver::languageVersion)
        .def("addStandardArgs", &Driver::addStandardArgs)
        .def(
            "parseCommandLine",
            [](Driver& self, std::string_view arg, CommandLine::ParseOptions parseOptions) {
                return self.parseCommandLine(arg, parseOptions);
            },
            "arg"_a, "parseOptions"_a = CommandLine::ParseOptions{})
        .def("processCommandFiles", &Driver::processCommandFiles, "fileName"_a, "makeRelative"_a,
             "separateUnit"_a)
        .def("processOptions", &Driver::processOptions)
        .def("runPreprocessor", &Driver::runPreprocessor, "includeComments"_a,
             "includeDirectives"_a, "obfuscateIds"_a, "useFixedObfuscationSeed"_a = false)
        .def("reportMacros", &Driver::reportMacros)
        .def("parseAllSources", &Driver::parseAllSources)
        .def("createOptionBag", &Driver::createOptionBag)
        .def("createCompilation", &Driver::createCompilation)
        .def("reportParseDiags", &Driver::reportParseDiags)
        .def("reportCompilation", &Driver::reportCompilation, "compilation"_a, "quiet"_a);

    py::class_<SourceOptions>(m, "SourceOptions")
        .def(py::init<>())
        .def_readwrite("numThreads", &SourceOptions::numThreads)
        .def_readwrite("singleUnit", &SourceOptions::singleUnit)
        .def_readwrite("onlyLint", &SourceOptions::onlyLint)
        .def_readwrite("librariesInheritMacros", &SourceOptions::librariesInheritMacros);

    py::class_<SourceLoader> sourceLoader(m, "SourceLoader");
    sourceLoader.def(py::init<SourceManager&>(), "sourceManager"_a)
        .def("addFiles", &SourceLoader::addFiles, "pattern"_a)
        .def("addLibraryFiles", &SourceLoader::addLibraryFiles, "libraryName"_a, "pattern"_a)
        .def("addSearchDirectories", &SourceLoader::addSearchDirectories, "pattern"_a)
        .def("addSearchExtension", &SourceLoader::addSearchExtension, "extension"_a)
        .def("addLibraryMaps", &SourceLoader::addLibraryMaps, "pattern"_a, "basePath"_a,
             "optionBag"_a)
        .def("addSeparateUnit", &SourceLoader::addSeparateUnit, "filePatterns"_a, "includePaths"_a,
             "defines"_a, "libraryName"_a)
        .def("loadSources", &SourceLoader::loadSources)
        .def("loadAndParseSources", &SourceLoader::loadAndParseSources, "optionBag"_a)
        .def_property_readonly("hasFiles", &SourceLoader::hasFiles)
        .def_property_readonly("libraryMaps", &SourceLoader::getLibraryMaps)
        .def_property_readonly("errors", &SourceLoader::getErrors);

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

    py::class_<SystemSubroutine, PySystemSubroutine, std::shared_ptr<SystemSubroutine>> systemSub(
        m, "SystemSubroutine");
    systemSub.def(py::init_alias<const std::string&, SubroutineKind>(), "name"_a, "kind"_a)
        .def_readwrite("name", &SystemSubroutine::name)
        .def_readwrite("kind", &SystemSubroutine::kind)
        .def_readwrite("hasOutputArgs", &SystemSubroutine::hasOutputArgs)
        .def_readwrite("withClauseMode", &SystemSubroutine::withClauseMode)
        .def("allowEmptyArgument", &SystemSubroutine::allowEmptyArgument, "argIndex"_a)
        .def("allowClockingArgument", &SystemSubroutine::allowClockingArgument, "argIndex"_a)
        .def("bindArgument", &SystemSubroutine::bindArgument, byrefint, "argIndex"_a, "context"_a,
             "syntax"_a, "previousArgs"_a)
        .def("checkArguments", &SystemSubroutine::checkArguments, byrefint, "context"_a, "args"_a,
             "range"_a, "iterOrThis"_a)
        .def("eval", &SystemSubroutine::eval, "context"_a, "args"_a, "range"_a, "callInfo"_a)
        .def("badArg", &SystemSubroutinePublicist::badArg, byrefint, "context"_a, "arg"_a)
        .def("checkArgCount", &SystemSubroutinePublicist::checkArgCount, "context"_a, "isMethod"_a,
             "args"_a, "callRange"_a, "min"_a, "max"_a)
        .def("kindStr", &SystemSubroutinePublicist::kindStr)
        .def("noHierarchical", &SystemSubroutinePublicist::noHierarchical, "context"_a, "expr"_a)
        .def("notConst", &SystemSubroutinePublicist::notConst, "context"_a, "range"_a)
        .def_static("unevaluatedContext", &SystemSubroutinePublicist::unevaluatedContext,
                    "sourceContext"_a)
        .def("__repr__", [](const SystemSubroutine& self) { return self.name; });

    py::enum_<SystemSubroutine::WithClauseMode>(systemSub, "WithClauseMode")
        .value("None_", SystemSubroutine::WithClauseMode::None)
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

    py::class_<SimpleSystemSubroutine, SystemSubroutine, PySimpleSystemSubroutine,
               std::shared_ptr<SimpleSystemSubroutine>>(m, "SimpleSystemSubroutine")
        .def(py::init_alias<const std::string&, SubroutineKind, size_t,
                            const std::vector<const Type*>&, const Type&, bool, bool>(),
             "name"_a, "kind"_a, "requiredArgs"_a, "argTypes"_a, "returnType"_a, "isMethod"_a,
             "isFirstArgLValue"_a = false);

    py::class_<NonConstantFunction, SimpleSystemSubroutine, std::shared_ptr<NonConstantFunction>>(
        m, "NonConstantFunction")
        .def(py::init<const std::string&, const Type&, size_t, const std::vector<const Type*>&,
                      bool>(),
             "name"_a, "returnType"_a, "requiredArgs"_a = 0,
             "argTypes"_a = std::vector<const Type*>{}, "isMethod"_a = false);
}

//------------------------------------------------------------------------------
// CompBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/ScriptSession.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

using namespace slang::driver;

void registerCompilation(nb::module_& m, nb::module_& ast, nb::module_& driver) {
    EXPOSE_ENUM(ast, VariableLifetime);
    EXPOSE_ENUM(ast, Visibility);
    EXPOSE_ENUM(ast, ArgumentDirection);
    EXPOSE_ENUM(ast, ProceduralBlockKind);
    EXPOSE_ENUM(ast, StatementBlockKind);
    EXPOSE_ENUM(ast, DefinitionKind);
    EXPOSE_ENUM(ast, UnconnectedDrive);
    EXPOSE_ENUM(ast, EdgeKind);
    EXPOSE_ENUM(ast, SubroutineKind);
    EXPOSE_ENUM(ast, AssertionKind);
    EXPOSE_ENUM(ast, ElabSystemTaskKind);
    EXPOSE_ENUM(ast, RandMode);
    EXPOSE_ENUM(ast, PrimitivePortDirection);

    nb::enum_<PreprocessOutputFlags>(m, "PreprocessOutputFlags", nb::is_arithmetic())
        .value("None_", PreprocessOutputFlags::None)
        .value("IncludeComments", PreprocessOutputFlags::IncludeComments)
        .value("IncludeDirectives", PreprocessOutputFlags::IncludeDirectives)
        .value("ObfuscateIds", PreprocessOutputFlags::ObfuscateIds)
        .value("UseFixedObfuscationSeed", PreprocessOutputFlags::UseFixedObfuscationSeed)
        .value("IncludeSourceInfo", PreprocessOutputFlags::IncludeSourceInfo);

    nb::enum_<MinTypMax>(ast, "MinTypMax")
        .value("Min", MinTypMax::Min)
        .value("Typ", MinTypMax::Typ)
        .value("Max", MinTypMax::Max);

    nb::enum_<CompilationFlags>(ast, "CompilationFlags", nb::is_arithmetic())
        .value("None_", CompilationFlags::None)
        .value("AllowHierarchicalConst", CompilationFlags::AllowHierarchicalConst)
        .value("RelaxEnumConversions", CompilationFlags::RelaxEnumConversions)
        .value("AllowUseBeforeDeclare", CompilationFlags::AllowUseBeforeDeclare)
        .value("AllowTopLevelIfacePorts", CompilationFlags::AllowTopLevelIfacePorts)
        .value("LintMode", CompilationFlags::LintMode)
        .value("IgnoreUnknownModules", CompilationFlags::IgnoreUnknownModules)
        .value("RelaxStringConversions", CompilationFlags::RelaxStringConversions)
        .value("AllowRecursiveImplicitCall", CompilationFlags::AllowRecursiveImplicitCall)
        .value("AllowBareValParamAssignment", CompilationFlags::AllowBareValParamAssignment)
        .value("AllowSelfDeterminedStreamConcat", CompilationFlags::AllowSelfDeterminedStreamConcat)
        .value("AllowMergingAnsiPorts", CompilationFlags::AllowMergingAnsiPorts)
        .value("DisableInstanceCaching", CompilationFlags::DisableInstanceCaching)
        .value("DisallowRefsToUnknownInstances", CompilationFlags::DisallowRefsToUnknownInstances)
        .value("AllowUnnamedGenerate", CompilationFlags::AllowUnnamedGenerate)
        .value("AllowVirtualIfaceWithOverride", CompilationFlags::AllowVirtualIfaceWithOverride)
        .value("AllowArrayConcatAssignPattern", CompilationFlags::AllowArrayConcatAssignPattern)
        .value("AllowCrossAutoBinMax", CompilationFlags::AllowCrossAutoBinMax)
        .value("AllowInvalidTop", CompilationFlags::AllowInvalidTop);

    nb::class_<CompilationOptions>(ast, "CompilationOptions")
        .def(nb::init<>())
        .def_rw("flags", &CompilationOptions::flags)
        .def_rw("maxInstanceDepth", &CompilationOptions::maxInstanceDepth)
        .def_rw("maxCheckerInstanceDepth", &CompilationOptions::maxCheckerInstanceDepth)
        .def_rw("maxGenerateSteps", &CompilationOptions::maxGenerateSteps)
        .def_rw("maxConstexprDepth", &CompilationOptions::maxConstexprDepth)
        .def_rw("maxConstexprSteps", &CompilationOptions::maxConstexprSteps)
        .def_rw("maxConstantSize", &CompilationOptions::maxConstantSize)
        .def_rw("maxConstexprBacktrace", &CompilationOptions::maxConstexprBacktrace)
        .def_rw("maxDefParamSteps", &CompilationOptions::maxDefParamSteps)
        .def_rw("maxDefParamBlocks", &CompilationOptions::maxDefParamBlocks)
        .def_rw("maxInstanceArray", &CompilationOptions::maxInstanceArray)
        .def_rw("maxEnumValues", &CompilationOptions::maxEnumValues)
        .def_rw("maxRecursiveClassSpecialization",
                &CompilationOptions::maxRecursiveClassSpecialization)
        .def_rw("maxUDPCoverageNotes", &CompilationOptions::maxUDPCoverageNotes)
        .def_rw("errorLimit", &CompilationOptions::errorLimit)
        .def_rw("typoCorrectionLimit", &CompilationOptions::typoCorrectionLimit)
        .def_rw("minTypMax", &CompilationOptions::minTypMax)
        .def_rw("languageVersion", &CompilationOptions::languageVersion)
        .def_rw("defaultTimeScale", &CompilationOptions::defaultTimeScale)
        .def_rw("topModules", &CompilationOptions::topModules)
        .def_rw("paramOverrides", &CompilationOptions::paramOverrides)
        .def_rw("defaultLiblist", &CompilationOptions::defaultLiblist);

    nb::class_<Compilation> comp(ast, "Compilation");
    comp.def(nb::init<>())
        .def(nb::init<const Bag&>(), "options"_a)
        .def_prop_ro("options", &Compilation::getOptions)
        .def_prop_ro("isFinalized", &Compilation::isFinalized)
        .def_prop_ro("isElaborated", &Compilation::isElaborated)
        .def_prop_ro("sourceManager", &Compilation::getSourceManager)
        .def_prop_ro("defaultLibrary", &Compilation::getDefaultLibrary)
        .def("addSyntaxTree", &Compilation::addSyntaxTree, "tree"_a)
        .def("getSyntaxTrees", &Compilation::getSyntaxTrees)
        .def("getRoot", nb::overload_cast<>(&Compilation::getRoot), byrefint)
        .def("addSystemSubroutine", &Compilation::addSystemSubroutine, nb::keep_alive<1, 2>(),
             "subroutine"_a)
        .def("addSystemMethod", &Compilation::addSystemMethod, nb::keep_alive<1, 3>(), "typeKind"_a,
             "method"_a)
        .def("getSystemSubroutine",
             nb::overload_cast<std::string_view>(&Compilation::getSystemSubroutine, nb::const_),
             byrefint, "name"_a)
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
        .def("getDPIExports",
             [](const Compilation& self) {
                 nb::list result;
                 auto parent = nb::cast(&self);
                 for (auto& entry : self.getDPIExports())
                     result.append(nb::cast(&entry, byrefint, parent));
                 return result;
             })
        .def("getAttributes",
             nb::overload_cast<const Symbol&>(&Compilation::getAttributes, nb::const_), byrefint,
             "symbol"_a)
        .def("getAttributes",
             nb::overload_cast<const Statement&>(&Compilation::getAttributes, nb::const_), byrefint,
             "stmt"_a)
        .def("getAttributes",
             nb::overload_cast<const Expression&>(&Compilation::getAttributes, nb::const_),
             byrefint, "expr"_a)
        .def("getAttributes",
             nb::overload_cast<const PortConnection&>(&Compilation::getAttributes, nb::const_),
             byrefint, "conn"_a)
        .def("getType", nb::overload_cast<SyntaxKind>(&Compilation::getType, nb::const_), byrefint,
             "kind"_a)
        .def("getNetType", &Compilation::getNetType, byrefint, "kind"_a)
        .def("freeze", &Compilation::freeze)
        .def("unfreeze", &Compilation::unfreeze)
        .def_prop_ro("defaultTimeScale", &Compilation::getDefaultTimeScale)
        .def_prop_ro("bitType", &Compilation::getBitType)
        .def_prop_ro("logicType", &Compilation::getLogicType)
        .def_prop_ro("intType", &Compilation::getIntType)
        .def_prop_ro("byteType", &Compilation::getByteType)
        .def_prop_ro("integerType", &Compilation::getIntegerType)
        .def_prop_ro("realType", &Compilation::getRealType)
        .def_prop_ro("shortRealType", &Compilation::getShortRealType)
        .def_prop_ro("stringType", &Compilation::getStringType)
        .def_prop_ro("voidType", &Compilation::getVoidType)
        .def_prop_ro("errorType", &Compilation::getErrorType)
        .def_prop_ro("unsignedIntType", &Compilation::getUnsignedIntType)
        .def_prop_ro("nullType", &Compilation::getNullType)
        .def_prop_ro("unboundedType", &Compilation::getUnboundedType)
        .def_prop_ro("typeRefType", &Compilation::getTypeRefType)
        .def_prop_ro("wireNetType", &Compilation::getWireNetType)
        .def_prop_ro("hasIssuedErrors", &Compilation::hasIssuedErrors)
        .def_prop_ro("hasFatalErrors", &Compilation::hasFatalErrors);

    nb::class_<Compilation::DefinitionLookupResult>(comp, "DefinitionLookupResult")
        .def(nb::init<>())
        .def_rw("definition", &Compilation::DefinitionLookupResult::definition)
        .def_rw("configRoot", &Compilation::DefinitionLookupResult::configRoot)
        .def_rw("configRule", &Compilation::DefinitionLookupResult::configRule);

    nb::class_<Compilation::DPIExport>(comp, "DPIExport")
        .def_ro("subroutine", &Compilation::DPIExport::subroutine)
        .def_ro("cIdentifier", &Compilation::DPIExport::cIdentifier)
        .def_ro("syntax", &Compilation::DPIExport::syntax);

    nb::class_<ScriptSession>(ast, "ScriptSession")
        .def(nb::init<>())
        .def_ro("compilation", &ScriptSession::compilation)
        .def("eval", &ScriptSession::eval, "text"_a)
        .def("evalExpression", &ScriptSession::evalExpression, "expr"_a)
        .def("evalStatement", &ScriptSession::evalStatement, "expr"_a)
        .def("getDiagnostics", &ScriptSession::getDiagnostics);

    nb::class_<CommandLine::ParseOptions>(driver, "CommandLineOptions")
        .def(nb::init<>())
        .def_rw("supportsComments", &CommandLine::ParseOptions::supportComments)
        .def_rw("ignoreProgramName", &CommandLine::ParseOptions::ignoreProgramName)
        .def_rw("expandEnvVars", &CommandLine::ParseOptions::expandEnvVars)
        .def_rw("ignoreDuplicates", &CommandLine::ParseOptions::ignoreDuplicates);

    nb::enum_<LanguageVersion>(m, "LanguageVersion")
        .value("v1364_2005", LanguageVersion::v1364_2005)
        .value("v1800_2017", LanguageVersion::v1800_2017)
        .value("v1800_2023", LanguageVersion::v1800_2023)
        .value("Default", LanguageVersion::Default);

    nb::class_<Driver> driverClass(driver, "Driver");

    nb::class_<Driver::CommandFileMetadata>(driverClass, "CommandFileMetadata")
        .def(nb::init<>())
        .def_rw("defines", &Driver::CommandFileMetadata::defines);

    driverClass.def(nb::init<>())
        .def_ro("sourceManager", &Driver::sourceManager)
        .def_ro("diagEngine", &Driver::diagEngine)
        .def_ro("textDiagClient", &Driver::textDiagClient)
        .def_ro("sourceLoader", &Driver::sourceLoader)
        .def_ro("syntaxTrees", &Driver::syntaxTrees)
        .def_rw("languageVersion", &Driver::languageVersion)
        .def_prop_ro("analysisOptions", &Driver::getAnalysisOptions)
        .def_prop_ro("commandFileMetadata", &Driver::getCommandFileMetadata)
        .def("addStandardArgs", &Driver::addStandardArgs)
        .def(
            "parseCommandLine",
            [](Driver& self, std::string_view arg, CommandLine::ParseOptions parseOptions) {
                return self.parseCommandLine(arg, parseOptions);
            },
            "arg"_a, "parseOptions"_a = CommandLine::ParseOptions{})
        .def("processCommandFiles", &Driver::processCommandFiles, "fileName"_a, "makeRelative"_a,
             "separateUnit"_a)
        .def("processOptions", &Driver::processOptions, "checkFiles"_a = true)
        .def("runPreprocessor", &Driver::runPreprocessor, "flags"_a)
        .def("reportMacros", &Driver::reportMacros, "groupByFile"_a = false)
        .def("optionallyWriteDepFiles", &Driver::optionallyWriteDepFiles)
        .def(
            "parseAllSources",
            [](Driver& self, nb::object bufferChangeCB) {
                if (bufferChangeCB.is_none()) {
                    nb::gil_scoped_release release;
                    return self.parseAllSources();
                }

                auto cb = nb::cast<nb::callable>(bufferChangeCB);
                auto wrapper = [&cb](BufferID buffer, bool isBack, bool isSkip) {
                    nb::gil_scoped_acquire acquire;
                    cb(buffer, isBack, isSkip);
                };

                nb::gil_scoped_release release;
                return self.parseAllSources(wrapper);
            },
            "bufferChangeCB"_a = nb::none())
        .def("createOptionBag", &Driver::createOptionBag)
        .def("createCompilation", &Driver::createCompilation, nb::keep_alive<0, 1>())
        .def("reportParseDiags", &Driver::reportParseDiags)
        .def("reportCompilation", &Driver::reportCompilation, "compilation"_a, "quiet"_a)
        .def("runAnalysis", &Driver::runAnalysis, "compilation"_a)
        .def("reportDiagnostics", &Driver::reportDiagnostics, "quiet"_a)
        .def("runFullCompilation", &Driver::runFullCompilation, "quiet"_a = false)
        .def("setTerminalColorsEnabled", &Driver::setTerminalColorsEnabled, "enable"_a);

    nb::class_<SourceOptions>(driver, "SourceOptions")
        .def(nb::init<>())
        .def_rw("numThreads", &SourceOptions::numThreads)
        .def_rw("singleUnit", &SourceOptions::singleUnit)
        .def_rw("onlyLint", &SourceOptions::onlyLint)
        .def_rw("librariesInheritMacros", &SourceOptions::librariesInheritMacros);

    nb::class_<SourceLoader> sourceLoader(driver, "SourceLoader");
    sourceLoader.def(nb::init<SourceManager&>(), "sourceManager"_a)
        .def("addFiles", &SourceLoader::addFiles, "pattern"_a)
        .def("addLibraryFiles", &SourceLoader::addLibraryFiles, "libraryName"_a, "pattern"_a)
        .def("addSearchDirectories", &SourceLoader::addSearchDirectories, "pattern"_a)
        .def("addSearchExtension", &SourceLoader::addSearchExtension, "extension"_a)
        .def("addLibraryMaps", &SourceLoader::addLibraryMaps, "pattern"_a, "basePath"_a,
             "optionBag"_a)
        .def("addSeparateUnit", &SourceLoader::addSeparateUnit, "filePatterns"_a, "includePaths"_a,
             "defines"_a, "libraryName"_a, "warningOptions"_a)
        .def("loadSources", &SourceLoader::loadSources)
        .def(
            "loadAndParseSources",
            [](SourceLoader& self, const Bag& optionBag) {
                return self.loadAndParseSources(optionBag);
            },
            "optionBag"_a)
        .def_prop_ro("hasFiles", &SourceLoader::hasFiles)
        .def_prop_ro("libraryMaps", &SourceLoader::getLibraryMaps)
        .def_prop_ro("errors", &SourceLoader::getErrors);

    class PySystemSubroutine : public SystemSubroutine {
    public:
        NB_TRAMPOLINE(SystemSubroutine, 5);

        PySystemSubroutine(std::string name, SubroutineKind kind) :
            SystemSubroutine(std::move(name), kind) {}

        bool allowEmptyArgument(size_t argIndex) const override {
            NB_OVERRIDE(allowEmptyArgument, argIndex);
        }

        bool allowClockingArgument(size_t argIndex) const override {
            NB_OVERRIDE(allowClockingArgument, argIndex);
        }

        const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                       const ExpressionSyntax& syntax,
                                       const Args& previousArgs) const override {
            NB_OVERRIDE(bindArgument, argIndex, context, syntax, previousArgs);
        }

        const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                                   const Expression* iterOrThis) const override {
            NB_OVERRIDE_PURE(checkArguments, context, args, range, iterOrThis);
        }

        ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                           const CallExpression::SystemCallInfo& callInfo) const override {
            NB_OVERRIDE_PURE(eval, context, args, range, callInfo);
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

    nb::class_<SystemSubroutine, PySystemSubroutine> systemSub(ast, "SystemSubroutine");
    systemSub.def(nb::init<const std::string&, SubroutineKind>(), "name"_a, "kind"_a)
        .def_rw("name", &SystemSubroutine::name)
        .def_rw("kind", &SystemSubroutine::kind)
        .def_rw("knownNameId", &SystemSubroutine::knownNameId)
        .def_rw("hasOutputArgs", &SystemSubroutine::hasOutputArgs)
        .def_rw("withClauseMode", &SystemSubroutine::withClauseMode)
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

    nb::enum_<SystemSubroutine::WithClauseMode>(systemSub, "WithClauseMode")
        .value("None_", SystemSubroutine::WithClauseMode::None)
        .value("Iterator", SystemSubroutine::WithClauseMode::Iterator)
        .value("Randomize", SystemSubroutine::WithClauseMode::Randomize);

    class PySimpleSystemSubroutine : public SimpleSystemSubroutine {
    public:
        NB_TRAMPOLINE(SimpleSystemSubroutine, 1);

        PySimpleSystemSubroutine(const std::string& name, SubroutineKind kind, size_t requiredArgs,
                                 const std::vector<const Type*>& argTypes, const Type& returnType,
                                 bool isMethod, bool isFirstArgLValue = false) :
            SimpleSystemSubroutine(name, kind, requiredArgs, argTypes, returnType, isMethod,
                                   isFirstArgLValue) {}

        ConstantValue eval(EvalContext& context, const Args& args, SourceRange range,
                           const CallExpression::SystemCallInfo& callInfo) const override {
            NB_OVERRIDE_PURE(eval, context, args, range, callInfo);
        }
    };

    nb::class_<SimpleSystemSubroutine, SystemSubroutine, PySimpleSystemSubroutine>(
        ast, "SimpleSystemSubroutine")
        .def(nb::init<const std::string&, SubroutineKind, size_t, const std::vector<const Type*>&,
                      const Type&, bool, bool>(),
             "name"_a, "kind"_a, "requiredArgs"_a, "argTypes"_a, "returnType"_a, "isMethod"_a,
             "isFirstArgLValue"_a = false);

    nb::class_<NonConstantFunction, SimpleSystemSubroutine>(ast, "NonConstantFunction")
        .def(nb::init<const std::string&, const Type&, size_t, const std::vector<const Type*>&,
                      bool>(),
             "name"_a, "returnType"_a, "requiredArgs"_a = 0,
             "argTypes"_a = std::vector<const Type*>{}, "isMethod"_a = false);
}

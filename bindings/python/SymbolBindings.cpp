//------------------------------------------------------------------------------
// SymbolBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "PyVisitors.h"
#include "pyslang.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/ast/types/NetType.h"
#include "slang/syntax/AllSyntax.h"

void registerSymbols(nb::module_& m) {
    EXPOSE_ENUM(m, SymbolKind);
    EXPOSE_ENUM(m, PulseStyleKind);
    EXPOSE_ENUM(m, SystemTimingCheckKind);

    nb::enum_<LookupFlags>(m, "LookupFlags", nb::is_arithmetic())
        .value("None_", LookupFlags::None)
        .value("Type", LookupFlags::Type)
        .value("AllowDeclaredAfter", LookupFlags::AllowDeclaredAfter)
        .value("DisallowWildcardImport", LookupFlags::DisallowWildcardImport)
        .value("NoUndeclaredError", LookupFlags::NoUndeclaredError)
        .value("NoUndeclaredErrorIfUninstantiated", LookupFlags::NoUndeclaredErrorIfUninstantiated)
        .value("AllowIncompleteForwardTypedefs", LookupFlags::AllowIncompleteForwardTypedefs)
        .value("NoSelectors", LookupFlags::NoSelectors)
        .value("AllowRoot", LookupFlags::AllowRoot)
        .value("AllowUnit", LookupFlags::AllowUnit)
        .value("IfacePortConn", LookupFlags::IfacePortConn)
        .value("StaticInitializer", LookupFlags::StaticInitializer)
        .value("ForceHierarchical", LookupFlags::ForceHierarchical)
        .value("TypeReference", LookupFlags::TypeReference)
        .value("AlwaysAllowUpward", LookupFlags::AlwaysAllowUpward)
        .value("DisallowUnitReferences", LookupFlags::DisallowUnitReferences)
        .value("AllowUnnamedGenerate", LookupFlags::AllowUnnamedGenerate);

    nb::enum_<LookupResultFlags>(m, "LookupResultFlags", nb::is_arithmetic())
        .value("None_", LookupResultFlags::None)
        .value("WasImported", LookupResultFlags::WasImported)
        .value("IsHierarchical", LookupResultFlags::IsHierarchical)
        .value("SuppressUndeclared", LookupResultFlags::SuppressUndeclared)
        .value("FromTypeParam", LookupResultFlags::FromTypeParam)
        .value("FromForwardTypedef", LookupResultFlags::FromForwardTypedef);

    nb::class_<LookupLocation>(m, "LookupLocation")
        .def(nb::init<>())
        .def(nb::init<const Scope*, uint32_t>(), "scope"_a, "index"_a)
        .def_prop_ro("scope", &LookupLocation::getScope)
        .def_prop_ro("index", &LookupLocation::getIndex)
        .def_static("before", &LookupLocation::before, "symbol"_a)
        .def_static("after", &LookupLocation::after, "symbol"_a)
        .def_ro_static("max", &LookupLocation::max)
        .def_ro_static("min", &LookupLocation::min)
        .def(nb::self == nb::self)
        .def(nb::self != nb::self);

    nb::class_<LookupResult> lookupResult(m, "LookupResult");
    lookupResult.def(nb::init<>())
        .def_ro("found", &LookupResult::found)
        .def_ro("systemSubroutine", &LookupResult::systemSubroutine)
        .def_ro("upwardCount", &LookupResult::upwardCount)
        .def_ro("flags", &LookupResult::flags)
        .def_ro("selectors", &LookupResult::selectors)
        .def_prop_ro("diagnostics", &LookupResult::getDiagnostics)
        .def_prop_ro("hasError", &LookupResult::hasError)
        .def("clear", &LookupResult::clear)
        .def("reportDiags", &LookupResult::reportDiags, "context"_a)
        .def("errorIfSelectors", &LookupResult::errorIfSelectors, "context"_a);

    nb::class_<LookupResult::MemberSelector>(lookupResult, "MemberSelector")
        .def_ro("name", &LookupResult::MemberSelector::name)
        .def_ro("dotLocation", &LookupResult::MemberSelector::dotLocation)
        .def_ro("nameRange", &LookupResult::MemberSelector::nameRange);

    nb::class_<Lookup>(m, "Lookup")
        .def_static("name", &Lookup::name, "syntax"_a, "context"_a, "flags"_a, "result"_a)
        .def_static("unqualified", &Lookup::unqualified, byrefint, "scope"_a, "name"_a,
                    "flags"_a = LookupFlags::None)
        .def_static("unqualifiedAt", &Lookup::unqualifiedAt, byrefint, "scope"_a, "name"_a,
                    "location"_a, "sourceRange"_a, "flags"_a = LookupFlags::None)
        .def_static("findClass", &Lookup::findClass, byrefint, "name"_a, "context"_a,
                    "requireInterfaceClass"_a = std::optional<DiagCode>{})
        .def_static("getContainingClass", &Lookup::getContainingClass, byrefint, "scope"_a)
        .def_static("getVisibility", &Lookup::getVisibility, "symbol"_a)
        .def_static("isVisibleFrom", &Lookup::isVisibleFrom, "symbol"_a, "scope"_a)
        .def_static("isAccessibleFrom", &Lookup::isAccessibleFrom, "target"_a, "sourceScope"_a)
        .def_static("ensureVisible", &Lookup::ensureVisible, "symbol"_a, "context"_a,
                    "sourceRange"_a)
        .def_static("ensureAccessible", &Lookup::ensureAccessible, "symbol"_a, "context"_a,
                    "sourceRange"_a)
        .def_static("findTempVar", &Lookup::findTempVar, "scope"_a, "symbol"_a, "name"_a,
                    "result"_a)
        .def_static("withinClassRandomize", &Lookup::withinClassRandomize, "context"_a, "syntax"_a,
                    "flags"_a, "result"_a)
        .def_static("findAssertionLocalVar", &Lookup::findAssertionLocalVar, "context"_a, "name"_a,
                    "result"_a);

    nb::class_<Symbol>(m, "Symbol")
        .def_ro("kind", &Symbol::kind)
        .def_ro("name", &Symbol::name)
        .def_ro("location", &Symbol::location)
        .def_prop_ro("parentScope", &Symbol::getParentScope)
        .def_prop_ro("syntax", &Symbol::getSyntax)
        .def_prop_ro("isScope", &Symbol::isScope)
        .def_prop_ro("isType", &Symbol::isType)
        .def_prop_ro("isValue", &Symbol::isValue)
        .def_prop_ro("declaredType", &Symbol::getDeclaredType)
        .def_prop_ro("declaringDefinition", &Symbol::getDeclaringDefinition)
        .def_prop_ro("randMode", &Symbol::getRandMode)
        .def_prop_ro("nextSibling", &Symbol::getNextSibling)
        .def_prop_ro("sourceLibrary", &Symbol::getSourceLibrary)
        .def_prop_ro("hierarchicalPath", &Symbol::getHierarchicalPath)
        .def_prop_ro("lexicalPath", &Symbol::getLexicalPath)
        .def("isDeclaredBefore",
             nb::overload_cast<const Symbol&>(&Symbol::isDeclaredBefore, nb::const_), "target"_a)
        .def("isDeclaredBefore",
             nb::overload_cast<LookupLocation>(&Symbol::isDeclaredBefore, nb::const_), "location"_a)
        .def("visit", &pyASTVisit<Symbol>, "f"_a = nb::none(), "lookup_table"_a = nb::none(),
             PyASTVisitor::doc)
        .def("__repr__", [](const Symbol& self) {
            return fmt::format("Symbol(SymbolKind.{}, \"{}\")", toString(self.kind), self.name);
        });

    nb::class_<Scope>(m, "Scope")
        .def_prop_ro("compilation", &Scope::getCompilation)
        .def_prop_ro("defaultNetType", &Scope::getDefaultNetType)
        .def_prop_ro("timeScale", &Scope::getTimeScale)
        .def_prop_ro("isProceduralContext", &Scope::isProceduralContext)
        .def_prop_ro("containingInstance", &Scope::getContainingInstance)
        .def_prop_ro("compilationUnit", &Scope::getCompilationUnit)
        .def_prop_ro("isUninstantiated", &Scope::isUninstantiated)
        .def(
            "find", [](const Scope& self, std::string_view arg) { return self.find(arg); },
            byrefint)
        .def(
            "lookupName",
            [](const Scope& self, std::string_view arg, LookupLocation location,
               bitmask<LookupFlags> flags) { return self.lookupName(arg, location, flags); },
            "name"_a, "location"_a = LookupLocation::max, "flags"_a = LookupFlags::None, byrefint)
        .def("__getitem__",
             [](const Scope& self, size_t idx) {
                 auto members = self.members();
                 members.advance(ptrdiff_t(idx));
                 if (members.begin() == members.end())
                     throw nb::index_error();

                 return nb::cast(&members.front(), byrefint, nb::cast(&self));
             })
        .def("__len__", [](const Scope& self) { return std::ranges::distance(self.members()); })
        .def(
            "__iter__",
            [](const Scope& self) {
                auto members = self.members();
                // See addScopeMethods: members() yields `const Symbol&`, which
                // must be handed out as non-owning references (not copied).
                return nb::make_iterator<nb::rv_policy::reference>(nb::type<Scope>(),
                                                                   "ScopeIterator", members.begin(),
                                                                   members.end());
            },
            nb::keep_alive<0, 1>());

    nb::class_<AttributeSymbol, Symbol>(m, "AttributeSymbol")
        .def_prop_ro("value", &AttributeSymbol::getValue);

    scopeClass<CompilationUnitSymbol, Symbol>(m, "CompilationUnitSymbol")
        .def_ro("timeScale", &CompilationUnitSymbol::timeScale);

    scopeClass<PackageSymbol, Symbol>(m, "PackageSymbol")
        .def_prop_ro("defaultNetType",
                     [](const PackageSymbol& self) { return &self.defaultNetType; })
        .def_ro("timeScale", &PackageSymbol::timeScale)
        .def_ro("defaultLifetime", &PackageSymbol::defaultLifetime)
        .def_ro("hasExportAll", &PackageSymbol::hasExportAll)
        .def("findForImport", &PackageSymbol::findForImport, byrefint, "name"_a);

    scopeClass<RootSymbol, Symbol>(m, "RootSymbol")
        .def_ro("topInstances", &RootSymbol::topInstances)
        .def_ro("compilationUnits", &RootSymbol::compilationUnits);

    nb::class_<DefinitionSymbol, Symbol>(m, "DefinitionSymbol")
        .def_ro("definitionKind", &DefinitionSymbol::definitionKind)
        .def_ro("defaultLifetime", &DefinitionSymbol::defaultLifetime)
        .def_ro("unconnectedDrive", &DefinitionSymbol::unconnectedDrive)
        .def_ro("cellDefine", &DefinitionSymbol::cellDefine)
        .def_ro("timeScale", &DefinitionSymbol::timeScale)
        .def_prop_ro("defaultNetType",
                     [](const DefinitionSymbol& self) { return &self.defaultNetType; })
        .def_prop_ro("instanceCount", &DefinitionSymbol::getInstanceCount)
        .def("getKindString", &DefinitionSymbol::getKindString)
        .def("getArticleKindString", &DefinitionSymbol::getArticleKindString)
        .def("__repr__", [](const DefinitionSymbol& self) {
            return fmt::format("DefinitionSymbol(\"{}\")", self.name);
        });

    nb::class_<ValueSymbol, Symbol>(m, "ValueSymbol")
        .def_prop_ro("type", &ValueSymbol::getType)
        .def_prop_ro("initializer", &ValueSymbol::getInitializer);

    nb::class_<EnumValueSymbol, ValueSymbol>(m, "EnumValueSymbol")
        .def_prop_ro("value", [](const EnumValueSymbol& self) { return self.getValue(); });

    nb::class_<ParameterSymbolBase>(m, "ParameterSymbolBase")
        .def_prop_ro("isLocalParam", &ParameterSymbolBase::isLocalParam)
        .def_prop_ro("isPortParam", &ParameterSymbolBase::isPortParam)
        .def_prop_ro("isBodyParam", &ParameterSymbolBase::isBodyParam);

    paramClass<ParameterSymbol, ValueSymbol>(m, "ParameterSymbol")
        .def_prop_ro("value", [](const ParameterSymbol& self) { return self.getValue(); })
        .def_prop_ro("isOverridden", &ParameterSymbol::isOverridden);

    paramClass<TypeParameterSymbol, Symbol>(m, "TypeParameterSymbol")
        .def_prop_ro("targetType", [](const TypeParameterSymbol& self) { return &self.targetType; })
        .def_prop_ro("typeAlias",
                     [](const TypeParameterSymbol& self) { return &self.getTypeAlias(); })
        .def_prop_ro("isOverridden", &TypeParameterSymbol::isOverridden);

    nb::class_<DefParamSymbol, Symbol>(m, "DefParamSymbol")
        .def_prop_ro("target", [](const DefParamSymbol& self) { return self.getTarget(); })
        .def_prop_ro("initializer",
                     [](const DefParamSymbol& self) { return &self.getInitializer(); })
        .def_prop_ro("value", [](const DefParamSymbol& self) { return self.getValue(); });

    nb::class_<SpecparamSymbol, ValueSymbol>(m, "SpecparamSymbol")
        .def_ro("isPathPulse", &SpecparamSymbol::isPathPulse)
        .def_prop_ro("value", [](const SpecparamSymbol& self) { return self.getValue(); })
        .def_prop_ro("pulseRejectLimit",
                     [](const SpecparamSymbol& self) { return self.getPulseRejectLimit(); })
        .def_prop_ro("pulseErrorLimit",
                     [](const SpecparamSymbol& self) { return self.getPulseErrorLimit(); })
        .def_prop_ro("pathSource", &SpecparamSymbol::getPathSource)
        .def_prop_ro("pathDest", &SpecparamSymbol::getPathDest);

    nb::enum_<VariableFlags>(m, "VariableFlags", nb::is_arithmetic())
        .value("None_", VariableFlags::None)
        .value("Const", VariableFlags::Const)
        .value("CompilerGenerated", VariableFlags::CompilerGenerated)
        .value("ImmutableCoverageOption", VariableFlags::ImmutableCoverageOption)
        .value("CoverageSampleFormal", VariableFlags::CoverageSampleFormal)
        .value("CheckerFreeVariable", VariableFlags::CheckerFreeVariable)
        .value("RefStatic", VariableFlags::RefStatic);

    nb::class_<VariableSymbol, ValueSymbol>(m, "VariableSymbol")
        .def_ro("lifetime", &VariableSymbol::lifetime)
        .def_ro("flags", &VariableSymbol::flags);

    nb::class_<FormalArgumentSymbol, VariableSymbol>(m, "FormalArgumentSymbol")
        .def_ro("direction", &FormalArgumentSymbol::direction)
        .def_prop_ro("defaultValue", &FormalArgumentSymbol::getDefaultValue);

    nb::class_<FieldSymbol, VariableSymbol>(m, "FieldSymbol")
        .def_ro("bitOffset", &FieldSymbol::bitOffset)
        .def_ro("fieldIndex", &FieldSymbol::fieldIndex)
        .def_ro("randMode", &FieldSymbol::randMode);

    nb::class_<NetSymbol, ValueSymbol> netSymbol(m, "NetSymbol");
    netSymbol.def_ro("expansionHint", &NetSymbol::expansionHint)
        .def_ro("isImplicit", &NetSymbol::isImplicit)
        .def_prop_ro("netType", [](const NetSymbol& self) { return &self.netType; })
        .def_prop_ro("delay", &NetSymbol::getDelay)
        .def_prop_ro("chargeStrength", &NetSymbol::getChargeStrength)
        .def_prop_ro("driveStrength", &NetSymbol::getDriveStrength);

    nb::enum_<NetSymbol::ExpansionHint>(netSymbol, "ExpansionHint")
        .value("None_", NetSymbol::None)
        .value("Vectored", NetSymbol::Vectored)
        .value("Scalared", NetSymbol::Scalared)
        .export_values();

    nb::class_<TempVarSymbol, VariableSymbol>(m, "TempVarSymbol");
    nb::class_<IteratorSymbol, TempVarSymbol>(m, "IteratorSymbol");
    nb::class_<PatternVarSymbol, TempVarSymbol>(m, "PatternVarSymbol");
    nb::class_<LocalAssertionVarSymbol, VariableSymbol>(m, "LocalAssertionVarSymbol");

    nb::class_<ClockingSkew>(m, "ClockingSkew")
        .def_ro("edge", &ClockingSkew::edge)
        .def_ro("delay", &ClockingSkew::delay)
        .def_prop_ro("hasValue", &ClockingSkew::hasValue);

    nb::class_<ClockVarSymbol, VariableSymbol>(m, "ClockVarSymbol")
        .def_ro("direction", &ClockVarSymbol::direction)
        .def_ro("inputSkew", &ClockVarSymbol::inputSkew)
        .def_ro("outputSkew", &ClockVarSymbol::outputSkew);

    nb::class_<ClassPropertySymbol, VariableSymbol>(m, "ClassPropertySymbol")
        .def_ro("visibility", &ClassPropertySymbol::visibility)
        .def_ro("randMode", &ClassPropertySymbol::randMode);

    nb::enum_<MethodFlags>(m, "MethodFlags", nb::is_arithmetic())
        .value("None_", MethodFlags::None)
        .value("Virtual", MethodFlags::Virtual)
        .value("Pure", MethodFlags::Pure)
        .value("Static", MethodFlags::Static)
        .value("Constructor", MethodFlags::Constructor)
        .value("InterfaceExtern", MethodFlags::InterfaceExtern)
        .value("ModportImport", MethodFlags::ModportImport)
        .value("ModportExport", MethodFlags::ModportExport)
        .value("DPIImport", MethodFlags::DPIImport)
        .value("DPIContext", MethodFlags::DPIContext)
        .value("BuiltIn", MethodFlags::BuiltIn)
        .value("Randomize", MethodFlags::Randomize)
        .value("ForkJoin", MethodFlags::ForkJoin)
        .value("DefaultedSuperArg", MethodFlags::DefaultedSuperArg)
        .value("Initial", MethodFlags::Initial)
        .value("Extends", MethodFlags::Extends)
        .value("Final", MethodFlags::Final);

    scopeClass<SubroutineSymbol, Symbol>(m, "SubroutineSymbol")
        .def_ro("defaultLifetime", &SubroutineSymbol::defaultLifetime)
        .def_ro("subroutineKind", &SubroutineSymbol::subroutineKind)
        .def_ro("visibility", &SubroutineSymbol::visibility)
        .def_ro("flags", &SubroutineSymbol::flags)
        .def_ro("thisVar", &SubroutineSymbol::thisVar)
        .def_ro("returnValVar", &SubroutineSymbol::returnValVar)
        .def_prop_ro("arguments", &SubroutineSymbol::getArguments)
        .def_prop_ro("body", &SubroutineSymbol::getBody)
        .def_prop_ro("returnType", &SubroutineSymbol::getReturnType)
        .def_prop_ro("override", &SubroutineSymbol::getOverride)
        .def_prop_ro("prototype", &SubroutineSymbol::getPrototype)
        .def_prop_ro("isVirtual", &SubroutineSymbol::isVirtual);

    auto methodProto = nb::class_<MethodPrototypeSymbol, Symbol>(m, "MethodPrototypeSymbol");
    addScopeMethods(methodProto);
    methodProto.def_ro("subroutineKind", &MethodPrototypeSymbol::subroutineKind)
        .def_ro("visibility", &MethodPrototypeSymbol::visibility)
        .def_ro("flags", &MethodPrototypeSymbol::flags)
        .def_prop_ro("arguments", &MethodPrototypeSymbol::getArguments)
        .def_prop_ro("returnType", &MethodPrototypeSymbol::getReturnType)
        .def_prop_ro("override", &MethodPrototypeSymbol::getOverride)
        .def_prop_ro("subroutine", &MethodPrototypeSymbol::getSubroutine)
        .def_prop_ro("isVirtual", &MethodPrototypeSymbol::isVirtual)
        .def_prop_ro("firstExternImpl", &MethodPrototypeSymbol::getFirstExternImpl);

    nb::class_<MethodPrototypeSymbol::ExternImpl>(methodProto, "ExternImpl")
        .def_ro("impl", &MethodPrototypeSymbol::ExternImpl::impl)
        .def_prop_ro("nextImpl", &MethodPrototypeSymbol::ExternImpl::getNextImpl);

    nb::class_<PortSymbol, Symbol>(m, "PortSymbol")
        .def_ro("internalSymbol", &PortSymbol::internalSymbol)
        .def_ro("externalLoc", &PortSymbol::externalLoc)
        .def_ro("direction", &PortSymbol::direction)
        .def_ro("isNullPort", &PortSymbol::isNullPort)
        .def_ro("isAnsiPort", &PortSymbol::isAnsiPort)
        .def_prop_ro("type", &PortSymbol::getType)
        .def_prop_ro("initializer", &PortSymbol::getInitializer)
        .def_prop_ro("internalExpr", &PortSymbol::getInternalExpr)
        .def_prop_ro("isNetPort", &PortSymbol::isNetPort);

    nb::class_<MultiPortSymbol, Symbol>(m, "MultiPortSymbol")
        .def_ro("ports", &MultiPortSymbol::ports)
        .def_ro("direction", &MultiPortSymbol::direction)
        .def_ro("isNullPort", &MultiPortSymbol::isNullPort)
        .def_prop_ro("type", &MultiPortSymbol::getType)
        .def_prop_ro("initializer", &MultiPortSymbol::getInitializer);

    nb::class_<InterfacePortSymbol, Symbol>(m, "InterfacePortSymbol")
        .def_ro("interfaceDef", &InterfacePortSymbol::interfaceDef)
        .def_ro("modport", &InterfacePortSymbol::modport)
        .def_ro("isGeneric", &InterfacePortSymbol::isGeneric)
        .def_prop_ro("declaredRange", &InterfacePortSymbol::getDeclaredRange)
        .def_prop_ro("connection", &InterfacePortSymbol::getConnection)
        .def_prop_ro("isInvalid", &InterfacePortSymbol::isInvalid);

    nb::class_<PortConnection>(m, "PortConnection")
        .def_prop_ro("ifaceConn", &PortConnection::getIfaceConn)
        .def_prop_ro("expression", &PortConnection::getExpression)
        .def_prop_ro("port", [](const PortConnection& self) { return &self.port; });

    nb::class_<InstanceSymbolBase, Symbol>(m, "InstanceSymbolBase")
        .def_ro("arrayPath", &InstanceSymbolBase::arrayPath)
        .def_prop_ro("arrayName", &InstanceSymbolBase::getArrayName);

    nb::class_<InstanceSymbol, InstanceSymbolBase>(m, "InstanceSymbol")
        .def_prop_ro("definition", &InstanceSymbol::getDefinition)
        .def_prop_ro("isModule", &InstanceSymbol::isModule)
        .def_prop_ro("isInterface", &InstanceSymbol::isInterface)
        .def_prop_ro("portConnections", &InstanceSymbol::getPortConnections)
        .def_prop_ro("body", [](const InstanceSymbol& self) { return &self.body; })
        .def_prop_ro("canonicalBody",
                     [](const InstanceSymbol& self) { return self.getCanonicalBody(); })
        .def("getPortConnection",
             nb::overload_cast<const PortSymbol&>(&InstanceSymbol::getPortConnection, nb::const_),
             byrefint, "port"_a)
        .def("getPortConnection",
             nb::overload_cast<const InterfacePortSymbol&>(&InstanceSymbol::getPortConnection,
                                                           nb::const_),
             byrefint, "port"_a);

    scopeClass<InstanceBodySymbol, Symbol>(m, "InstanceBodySymbol")
        .def_ro("parentInstance", &InstanceBodySymbol::parentInstance)
        .def_prop_ro("parameters",
                     [](const InstanceBodySymbol& self) {
                         // getParameters() yields ParameterSymbolBase pointers, which
                         // nanobind cannot downcast on their own: ParameterSymbolBase is a
                         // secondary base at a nonzero offset (see the type_hook note in
                         // pyslang.h). Build the list from each parameter's embedded `symbol`
                         // subobject instead. For ParameterSymbol or TypeParameterSymbol that
                         // Symbol is the concrete object at offset 0, so the Symbol type_hook
                         // downcasts it to the concrete parameter symbol type in Python. The
                         // symbols are exposed non-owning (byref); they live in the
                         // compilation arena. Appending directly avoids an intermediate
                         // std::vector.
                         nb::list result;
                         for (const ParameterSymbolBase* param : self.getParameters())
                             result.append(nb::cast(&param->symbol, byref));
                         return result;
                     })
        .def_prop_ro("portList", &InstanceBodySymbol::getPortList)
        .def_prop_ro("definition", &InstanceBodySymbol::getDefinition)
        .def("findPort", &InstanceBodySymbol::findPort, byrefint, "portName"_a)
        .def("hasSameType", &InstanceBodySymbol::hasSameType, "other"_a);

    scopeClass<InstanceArraySymbol, Symbol>(m, "InstanceArraySymbol")
        .def_ro("elements", &InstanceArraySymbol::elements)
        .def_ro("range", &InstanceArraySymbol::range)
        .def_prop_ro("arrayName", &InstanceArraySymbol::getArrayName);

    nb::class_<UninstantiatedDefSymbol, Symbol>(m, "UninstantiatedDefSymbol")
        .def_ro("definitionName", &UninstantiatedDefSymbol::definitionName)
        .def_ro("paramExpressions", &UninstantiatedDefSymbol::paramExpressions)
        .def_prop_ro("portConnections", &UninstantiatedDefSymbol::getPortConnections)
        .def_prop_ro("portNames", &UninstantiatedDefSymbol::getPortNames)
        .def_prop_ro("isChecker", &UninstantiatedDefSymbol::isChecker);

    nb::class_<PrimitiveInstanceSymbol, InstanceSymbolBase>(m, "PrimitiveInstanceSymbol")
        .def_prop_ro("primitiveType",
                     [](const PrimitiveInstanceSymbol& self) { return &self.primitiveType; })
        .def_prop_ro("portConnections", &PrimitiveInstanceSymbol::getPortConnections)
        .def_prop_ro("delay", &PrimitiveInstanceSymbol::getDelay)
        .def_prop_ro("driveStrength", &PrimitiveInstanceSymbol::getDriveStrength);

    nb::class_<CheckerInstanceSymbol, InstanceSymbolBase> checkerInst(m, "CheckerInstanceSymbol");
    checkerInst.def_prop_ro("body", [](const CheckerInstanceSymbol& self) { return &self.body; })
        .def_prop_ro("portConnections", &CheckerInstanceSymbol::getPortConnections);

    nb::class_<CheckerInstanceSymbol::Connection>(checkerInst, "Connection")
        .def_prop_ro("formal",
                     [](const CheckerInstanceSymbol::Connection& self) { return &self.formal; })
        .def_prop_ro("outputInitialExpr", &CheckerInstanceSymbol::Connection::getOutputInitialExpr)
        .def_ro("actual", &CheckerInstanceSymbol::Connection::actual)
        .def_ro("attributes", &CheckerInstanceSymbol::Connection::attributes);

    scopeClass<CheckerInstanceBodySymbol, Symbol>(m, "CheckerInstanceBodySymbol")
        .def_ro("parentInstance", &CheckerInstanceBodySymbol::parentInstance)
        .def_prop_ro("checker",
                     [](const CheckerInstanceBodySymbol& self) { return &self.checker; });

    scopeClass<StatementBlockSymbol, Symbol>(m, "StatementBlockSymbol")
        .def_ro("blockKind", &StatementBlockSymbol::blockKind)
        .def_ro("defaultLifetime", &StatementBlockSymbol::defaultLifetime);

    nb::class_<ProceduralBlockSymbol, Symbol>(m, "ProceduralBlockSymbol")
        .def_ro("procedureKind", &ProceduralBlockSymbol::procedureKind)
        .def_prop_ro("isSingleDriverBlock", &ProceduralBlockSymbol::isSingleDriverBlock)
        .def_prop_ro("body", &ProceduralBlockSymbol::getBody)
        .def_prop_ro("blocks", &ProceduralBlockSymbol::getBlocks);

    EXPOSE_ENUM(m, GenerateBranchKind);

    scopeClass<GenerateBlockSymbol, Symbol>(m, "GenerateBlockSymbol")
        .def_ro("constructIndex", &GenerateBlockSymbol::constructIndex)
        .def_ro("isUninstantiated", &GenerateBlockSymbol::isUninstantiated)
        .def_ro("branchKind", &GenerateBlockSymbol::branchKind)
        .def_ro("caseItemExpressions", &GenerateBlockSymbol::caseItemExpressions)
        .def_prop_ro("arrayIndex", &GenerateBlockSymbol::getArrayIndex)
        .def_prop_ro("conditionExpression", &GenerateBlockSymbol::getConditionExpression)
        .def_prop_ro("externalName", &GenerateBlockSymbol::getExternalName);

    scopeClass<GenerateBlockArraySymbol, Symbol>(m, "GenerateBlockArraySymbol")
        .def_ro("constructIndex", &GenerateBlockArraySymbol::constructIndex)
        .def_ro("entries", &GenerateBlockArraySymbol::entries)
        .def_ro("valid", &GenerateBlockArraySymbol::valid)
        .def_ro("initialExpression", &GenerateBlockArraySymbol::initialExpression)
        .def_ro("stopExpression", &GenerateBlockArraySymbol::stopExpression)
        .def_ro("iterExpression", &GenerateBlockArraySymbol::iterExpression)
        .def_ro("loopVariable", &GenerateBlockArraySymbol::loopVariable)
        .def_prop_ro("externalName", &GenerateBlockArraySymbol::getExternalName);

    nb::class_<EmptyMemberSymbol, Symbol>(m, "EmptyMemberSymbol");
    nb::class_<GenvarSymbol, Symbol>(m, "GenvarSymbol");
    scopeClass<SpecifyBlockSymbol, Symbol>(m, "SpecifyBlockSymbol");
    scopeClass<AnonymousProgramSymbol, Symbol>(m, "AnonymousProgramSymbol");

    nb::class_<NetAliasSymbol, Symbol>(m, "NetAliasSymbol")
        .def_prop_ro("netReferences", &NetAliasSymbol::getNetReferences);

    nb::class_<TransparentMemberSymbol, Symbol>(m, "TransparentMemberSymbol")
        .def_prop_ro("wrapped", [](const TransparentMemberSymbol& self) { return &self.wrapped; });

    nb::class_<ExplicitImportSymbol, Symbol>(m, "ExplicitImportSymbol")
        .def_ro("packageName", &ExplicitImportSymbol::packageName)
        .def_ro("importName", &ExplicitImportSymbol::importName)
        .def_prop_ro("package", &ExplicitImportSymbol::package)
        .def_prop_ro("importedSymbol", &ExplicitImportSymbol::importedSymbol);

    nb::class_<WildcardImportSymbol, Symbol>(m, "WildcardImportSymbol")
        .def_ro("packageName", &WildcardImportSymbol::packageName)
        .def_prop_ro("package", &WildcardImportSymbol::getPackage);

    nb::class_<ModportPortSymbol, ValueSymbol>(m, "ModportPortSymbol")
        .def_ro("direction", &ModportPortSymbol::direction)
        .def_ro("internalSymbol", &ModportPortSymbol::internalSymbol)
        .def_ro("explicitConnection", &ModportPortSymbol::explicitConnection);

    nb::class_<ModportClockingSymbol, Symbol>(m, "ModportClockingSymbol")
        .def_ro("target", &ModportClockingSymbol::target);

    scopeClass<ModportSymbol, Symbol>(m, "ModportSymbol")
        .def_ro("hasExports", &ModportSymbol::hasExports);

    nb::class_<ContinuousAssignSymbol, Symbol>(m, "ContinuousAssignSymbol")
        .def_prop_ro("assignment", &ContinuousAssignSymbol::getAssignment)
        .def_prop_ro("delay", &ContinuousAssignSymbol::getDelay)
        .def_prop_ro("driveStrength", &ContinuousAssignSymbol::getDriveStrength);

    nb::class_<ElabSystemTaskSymbol, Symbol>(m, "ElabSystemTaskSymbol")
        .def_ro("taskKind", &ElabSystemTaskSymbol::taskKind)
        .def_prop_ro("message", &ElabSystemTaskSymbol::getMessage)
        .def_prop_ro("assertCondition", &ElabSystemTaskSymbol::getAssertCondition);

    nb::class_<PrimitivePortSymbol, ValueSymbol>(m, "PrimitivePortSymbol")
        .def_ro("direction", &PrimitivePortSymbol::direction);

    auto primitiveSym = nb::class_<PrimitiveSymbol, Symbol>(m, "PrimitiveSymbol");
    addScopeMethods(primitiveSym);
    primitiveSym.def_ro("ports", &PrimitiveSymbol::ports)
        .def_ro("initVal", &PrimitiveSymbol::initVal)
        .def_ro("primitiveKind", &PrimitiveSymbol::primitiveKind)
        .def_ro("isSequential", &PrimitiveSymbol::isSequential)
        .def_ro("table", &PrimitiveSymbol::table);

    nb::enum_<PrimitiveSymbol::PrimitiveKind>(primitiveSym, "PrimitiveKind")
        .value("UserDefined", PrimitiveSymbol::PrimitiveKind::UserDefined)
        .value("Fixed", PrimitiveSymbol::PrimitiveKind::Fixed)
        .value("NInput", PrimitiveSymbol::PrimitiveKind::NInput)
        .value("NOutput", PrimitiveSymbol::PrimitiveKind::NOutput)
        .export_values();

    nb::class_<PrimitiveSymbol::TableEntry>(primitiveSym, "TableEntry")
        .def_ro("inputs", &PrimitiveSymbol::TableEntry::inputs)
        .def_ro("state", &PrimitiveSymbol::TableEntry::state)
        .def_ro("output", &PrimitiveSymbol::TableEntry::output);

    nb::class_<AssertionPortSymbol, Symbol>(m, "AssertionPortSymbol")
        .def_ro("direction", &AssertionPortSymbol::direction)
        .def_prop_ro("isLocalVar", &AssertionPortSymbol::isLocalVar)
        .def_prop_ro("type",
                     [](const AssertionPortSymbol& self) { return &self.declaredType.getType(); });

    scopeClass<SequenceSymbol, Symbol>(m, "SequenceSymbol").def_ro("ports", &SequenceSymbol::ports);

    scopeClass<PropertySymbol, Symbol>(m, "PropertySymbol").def_ro("ports", &PropertySymbol::ports);

    scopeClass<LetDeclSymbol, Symbol>(m, "LetDeclSymbol").def_ro("ports", &LetDeclSymbol::ports);

    scopeClass<CheckerSymbol, Symbol>(m, "CheckerSymbol").def_ro("ports", &CheckerSymbol::ports);

    scopeClass<ClockingBlockSymbol, Symbol>(m, "ClockingBlockSymbol")
        .def_prop_ro("event", &ClockingBlockSymbol::getEvent)
        .def_prop_ro("defaultInputSkew", &ClockingBlockSymbol::getDefaultInputSkew)
        .def_prop_ro("defaultOutputSkew", &ClockingBlockSymbol::getDefaultOutputSkew);

    auto randSeq = nb::class_<RandSeqProductionSymbol, Symbol>(m, "RandSeqProductionSymbol");
    addScopeMethods(randSeq);
    randSeq.def_ro("arguments", &RandSeqProductionSymbol::arguments)
        .def_prop_ro("rules", &RandSeqProductionSymbol::getRules)
        .def_prop_ro("returnType", &RandSeqProductionSymbol::getReturnType);

    nb::enum_<RandSeqProductionSymbol::ProdKind>(randSeq, "ProdKind")
        .value("Item", RandSeqProductionSymbol::ProdKind::Item)
        .value("CodeBlock", RandSeqProductionSymbol::ProdKind::CodeBlock)
        .value("IfElse", RandSeqProductionSymbol::ProdKind::IfElse)
        .value("Repeat", RandSeqProductionSymbol::ProdKind::Repeat)
        .value("Case", RandSeqProductionSymbol::ProdKind::Case);

    nb::class_<RandSeqProductionSymbol::ProdBase>(randSeq, "ProdBase")
        .def_ro("kind", &RandSeqProductionSymbol::ProdBase::kind);

    nb::class_<RandSeqProductionSymbol::ProdItem, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                     "ProdItem")
        .def_ro("target", &RandSeqProductionSymbol::ProdItem::target)
        .def_ro("args", &RandSeqProductionSymbol::ProdItem::args);

    nb::class_<RandSeqProductionSymbol::CodeBlockProd, RandSeqProductionSymbol::ProdBase>(
        randSeq, "CodeBlockProd")
        .def_ro("block", &RandSeqProductionSymbol::CodeBlockProd::block);

    nb::class_<RandSeqProductionSymbol::IfElseProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                       "IfElseProd")
        .def_ro("expr", &RandSeqProductionSymbol::IfElseProd::expr)
        .def_ro("ifItem", &RandSeqProductionSymbol::IfElseProd::ifItem)
        .def_ro("elseItem", &RandSeqProductionSymbol::IfElseProd::elseItem);

    nb::class_<RandSeqProductionSymbol::RepeatProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                       "RepeatProd")
        .def_ro("expr", &RandSeqProductionSymbol::RepeatProd::expr)
        .def_ro("item", &RandSeqProductionSymbol::RepeatProd::item);

    nb::class_<RandSeqProductionSymbol::CaseItem>(randSeq, "CaseItem")
        .def_ro("expressions", &RandSeqProductionSymbol::CaseItem::expressions)
        .def_ro("item", &RandSeqProductionSymbol::CaseItem::item);

    nb::class_<RandSeqProductionSymbol::CaseProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                     "CaseProd")
        .def_ro("expr", &RandSeqProductionSymbol::CaseProd::expr)
        .def_ro("items", &RandSeqProductionSymbol::CaseProd::items)
        .def_ro("defaultItem", &RandSeqProductionSymbol::CaseProd::defaultItem);

    nb::class_<RandSeqProductionSymbol::Rule>(randSeq, "Rule")
        .def_ro("ruleBlock", &RandSeqProductionSymbol::Rule::ruleBlock)
        .def_ro("prods", &RandSeqProductionSymbol::Rule::prods)
        .def_ro("weightExpr", &RandSeqProductionSymbol::Rule::weightExpr)
        .def_ro("randJoinExpr", &RandSeqProductionSymbol::Rule::randJoinExpr)
        .def_ro("codeBlock", &RandSeqProductionSymbol::Rule::codeBlock)
        .def_ro("isRandJoin", &RandSeqProductionSymbol::Rule::isRandJoin);

    nb::class_<TimingPathSymbol, Symbol> timingPath(m, "TimingPathSymbol");
    timingPath.def_ro("connectionKind", &TimingPathSymbol::connectionKind)
        .def_ro("polarity", &TimingPathSymbol::polarity)
        .def_ro("edgePolarity", &TimingPathSymbol::edgePolarity)
        .def_ro("edgeIdentifier", &TimingPathSymbol::edgeIdentifier)
        .def_ro("isStateDependent", &TimingPathSymbol::isStateDependent)
        .def_prop_ro("edgeSourceExpr", &TimingPathSymbol::getEdgeSourceExpr)
        .def_prop_ro("conditionExpr", &TimingPathSymbol::getConditionExpr)
        .def_prop_ro("inputs", &TimingPathSymbol::getInputs)
        .def_prop_ro("outputs", &TimingPathSymbol::getOutputs)
        .def_prop_ro("delays", &TimingPathSymbol::getDelays);

    nb::enum_<TimingPathSymbol::ConnectionKind>(timingPath, "ConnectionKind")
        .value("Full", TimingPathSymbol::ConnectionKind::Full)
        .value("Parallel", TimingPathSymbol::ConnectionKind::Parallel);

    nb::enum_<TimingPathSymbol::Polarity>(timingPath, "Polarity")
        .value("Unknown", TimingPathSymbol::Polarity::Unknown)
        .value("Positive", TimingPathSymbol::Polarity::Positive)
        .value("Negative", TimingPathSymbol::Polarity::Negative);

    nb::class_<PulseStyleSymbol, Symbol>(m, "PulseStyleSymbol")
        .def_ro("pulseStyleKind", &PulseStyleSymbol::pulseStyleKind)
        .def_prop_ro("terminals", &PulseStyleSymbol::getTerminals);

    nb::class_<SystemTimingCheckSymbol, Symbol> timingCheck(m, "SystemTimingCheckSymbol");
    timingCheck.def_ro("timingCheckKind", &SystemTimingCheckSymbol::timingCheckKind)
        .def_prop_ro("arguments", &SystemTimingCheckSymbol::getArguments);

    nb::class_<SystemTimingCheckSymbol::Arg>(timingCheck, "Arg")
        .def_ro("expr", &SystemTimingCheckSymbol::Arg::expr)
        .def_ro("condition", &SystemTimingCheckSymbol::Arg::condition)
        .def_ro("edge", &SystemTimingCheckSymbol::Arg::edge)
        .def_ro("edgeDescriptors", &SystemTimingCheckSymbol::Arg::edgeDescriptors);

    nb::class_<CoverageOptionSetter>(m, "CoverageOptionSetter")
        .def_prop_ro("isTypeOption", &CoverageOptionSetter::isTypeOption)
        .def_prop_ro("name", &CoverageOptionSetter::getName)
        .def_prop_ro("expression", &CoverageOptionSetter::getExpression);

    scopeClass<CovergroupBodySymbol, Symbol>(m, "CovergroupBodySymbol")
        .def_ro("options", &CovergroupBodySymbol::options);

    nb::class_<CoverageBinSymbol, Symbol> coverageBinSym(m, "CoverageBinSymbol");
    coverageBinSym.def_ro("binsKind", &CoverageBinSymbol::binsKind)
        .def_ro("isArray", &CoverageBinSymbol::isArray)
        .def_ro("isWildcard", &CoverageBinSymbol::isWildcard)
        .def_ro("isDefault", &CoverageBinSymbol::isDefault)
        .def_ro("isDefaultSequence", &CoverageBinSymbol::isDefaultSequence)
        .def_prop_ro("iffExpr", &CoverageBinSymbol::getIffExpr)
        .def_prop_ro("numberOfBinsExpr", &CoverageBinSymbol::getNumberOfBinsExpr)
        .def_prop_ro("setCoverageExpr", &CoverageBinSymbol::getSetCoverageExpr)
        .def_prop_ro("withExpr", &CoverageBinSymbol::getWithExpr)
        .def_prop_ro("crossSelectExpr", &CoverageBinSymbol::getCrossSelectExpr)
        .def_prop_ro("values", &CoverageBinSymbol::getValues);

    nb::class_<CoverageBinSymbol::TransRangeList> transRangeList(coverageBinSym, "TransRangeList");
    transRangeList.def_ro("items", &CoverageBinSymbol::TransRangeList::items)
        .def_ro("repeatFrom", &CoverageBinSymbol::TransRangeList::repeatFrom)
        .def_ro("repeatTo", &CoverageBinSymbol::TransRangeList::repeatTo)
        .def_ro("repeatKind", &CoverageBinSymbol::TransRangeList::repeatKind);

    nb::enum_<CoverageBinSymbol::TransRangeList::RepeatKind>(transRangeList, "RepeatKind",
                                                             "enum.Enum")
        .value("None_", CoverageBinSymbol::TransRangeList::None)
        .value("Consecutive", CoverageBinSymbol::TransRangeList::Consecutive)
        .value("Nonconsecutive", CoverageBinSymbol::TransRangeList::Nonconsecutive)
        .value("GoTo", CoverageBinSymbol::TransRangeList::GoTo)
        .export_values();

    nb::enum_<CoverageBinSymbol::BinKind>(coverageBinSym, "BinKind")
        .value("Bins", CoverageBinSymbol::Bins)
        .value("IllegalBins", CoverageBinSymbol::IllegalBins)
        .value("IgnoreBins", CoverageBinSymbol::IgnoreBins)
        .export_values();

    scopeClass<CoverpointSymbol, Symbol>(m, "CoverpointSymbol")
        .def_ro("options", &CoverpointSymbol::options)
        .def_prop_ro("type", &CoverpointSymbol::getType)
        .def_prop_ro("coverageExpr", &CoverpointSymbol::getCoverageExpr)
        .def_prop_ro("iffExpr", &CoverpointSymbol::getIffExpr);

    scopeClass<CoverCrossBodySymbol, Symbol>(m, "CoverCrossBodySymbol")
        .def_ro("crossQueueType", &CoverCrossBodySymbol::crossQueueType);

    scopeClass<CoverCrossSymbol, Symbol>(m, "CoverCrossSymbol")
        .def_ro("options", &CoverCrossSymbol::options)
        .def_ro("targets", &CoverCrossSymbol::targets)
        .def_prop_ro("iffExpr", &CoverCrossSymbol::getIffExpr);

    scopeClass<ConfigBlockSymbol, Symbol>(m, "ConfigBlockSymbol");
}

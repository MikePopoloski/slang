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

void registerSymbols(py::module_& m) {
    EXPOSE_ENUM(m, SymbolKind);
    EXPOSE_ENUM(m, PulseStyleKind);
    EXPOSE_ENUM(m, SystemTimingCheckKind);

    py::enum_<LookupFlags>(m, "LookupFlags")
        .value("None_", LookupFlags::None)
        .value("Type", LookupFlags::Type)
        .value("AllowDeclaredAfter", LookupFlags::AllowDeclaredAfter)
        .value("DisallowWildcardImport", LookupFlags::DisallowWildcardImport)
        .value("NoUndeclaredError", LookupFlags::NoUndeclaredError)
        .value("NoUndeclaredErrorIfUninstantiated", LookupFlags::NoUndeclaredErrorIfUninstantiated)
        .value("AllowIncompleteForwardTypedefs", LookupFlags::AllowIncompleteForwardTypedefs)
        .value("NoParentScope", LookupFlags::NoParentScope)
        .value("NoSelectors", LookupFlags::NoSelectors)
        .value("AllowRoot", LookupFlags::AllowRoot)
        .value("AllowUnit", LookupFlags::AllowUnit)
        .value("IfacePortConn", LookupFlags::IfacePortConn)
        .value("StaticInitializer", LookupFlags::StaticInitializer)
        .value("ForceHierarchical", LookupFlags::ForceHierarchical)
        .value("TypeReference", LookupFlags::TypeReference)
        .value("AlwaysAllowUpward", LookupFlags::AlwaysAllowUpward)
        .value("DisallowUnitReferences", LookupFlags::DisallowUnitReferences);

    py::enum_<LookupResultFlags>(m, "LookupResultFlags")
        .value("None_", LookupResultFlags::None)
        .value("WasImported", LookupResultFlags::WasImported)
        .value("IsHierarchical", LookupResultFlags::IsHierarchical)
        .value("SuppressUndeclared", LookupResultFlags::SuppressUndeclared)
        .value("FromTypeParam", LookupResultFlags::FromTypeParam)
        .value("FromForwardTypedef", LookupResultFlags::FromForwardTypedef);

    py::class_<LookupLocation>(m, "LookupLocation")
        .def(py::init<>())
        .def(py::init<const Scope*, uint32_t>(), "scope"_a, "index"_a)
        .def_property_readonly("scope", &LookupLocation::getScope)
        .def_property_readonly("index", &LookupLocation::getIndex)
        .def_static("before", &LookupLocation::before, "symbol"_a)
        .def_static("after", &LookupLocation::after, "symbol"_a)
        .def_readonly_static("max", &LookupLocation::max)
        .def_readonly_static("min", &LookupLocation::min)
        .def(py::self == py::self)
        .def(py::self != py::self);

    py::class_<LookupResult> lookupResult(m, "LookupResult");
    lookupResult.def(py::init<>())
        .def_readonly("found", &LookupResult::found)
        .def_readonly("systemSubroutine", &LookupResult::systemSubroutine)
        .def_readonly("upwardCount", &LookupResult::upwardCount)
        .def_readonly("flags", &LookupResult::flags)
        .def_readonly("selectors", &LookupResult::selectors)
        .def_property_readonly("diagnostics", &LookupResult::getDiagnostics)
        .def_property_readonly("hasError", &LookupResult::hasError)
        .def("clear", &LookupResult::clear)
        .def("reportDiags", &LookupResult::reportDiags, "context"_a)
        .def("errorIfSelectors", &LookupResult::errorIfSelectors, "context"_a);

    py::class_<LookupResult::MemberSelector>(lookupResult, "MemberSelector")
        .def_readonly("name", &LookupResult::MemberSelector::name)
        .def_readonly("dotLocation", &LookupResult::MemberSelector::dotLocation)
        .def_readonly("nameRange", &LookupResult::MemberSelector::nameRange);

    py::class_<Lookup>(m, "Lookup")
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

    py::class_<Symbol>(m, "Symbol")
        .def_readonly("kind", &Symbol::kind)
        .def_readonly("name", &Symbol::name)
        .def_readonly("location", &Symbol::location)
        .def_property_readonly("parentScope", &Symbol::getParentScope)
        .def_property_readonly("syntax", &Symbol::getSyntax)
        .def_property_readonly("isScope", &Symbol::isScope)
        .def_property_readonly("isType", &Symbol::isType)
        .def_property_readonly("isValue", &Symbol::isValue)
        .def_property_readonly("declaredType", &Symbol::getDeclaredType)
        .def_property_readonly("declaringDefinition", &Symbol::getDeclaringDefinition)
        .def_property_readonly("randMode", &Symbol::getRandMode)
        .def_property_readonly("nextSibling", &Symbol::getNextSibling)
        .def_property_readonly("sourceLibrary", &Symbol::getSourceLibrary)
        .def_property_readonly("hierarchicalPath",
                               [](const Symbol& self) {
                                   std::string str;
                                   self.getHierarchicalPath(str);
                                   return str;
                               })
        .def_property_readonly("lexicalPath",
                               [](const Symbol& self) {
                                   std::string str;
                                   self.getLexicalPath(str);
                                   return str;
                               })
        .def("isDeclaredBefore",
             py::overload_cast<const Symbol&>(&Symbol::isDeclaredBefore, py::const_), "target"_a)
        .def("isDeclaredBefore",
             py::overload_cast<LookupLocation>(&Symbol::isDeclaredBefore, py::const_), "location"_a)
        .def("visit", &pyASTVisit<Symbol>, "f"_a, PyASTVisitor::doc)
        .def("__repr__", [](const Symbol& self) {
            return fmt::format("Symbol(SymbolKind.{}, \"{}\")", toString(self.kind), self.name);
        });

    py::class_<Scope>(m, "Scope")
        .def_property_readonly("compilation", &Scope::getCompilation)
        .def_property_readonly("defaultNetType", &Scope::getDefaultNetType)
        .def_property_readonly("timeScale", &Scope::getTimeScale)
        .def_property_readonly("isProceduralContext", &Scope::isProceduralContext)
        .def_property_readonly("containingInstance", &Scope::getContainingInstance)
        .def_property_readonly("compilationUnit", &Scope::getCompilationUnit)
        .def_property_readonly("isUninstantiated", &Scope::isUninstantiated)
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
                     throw py::index_error();

                 return py::cast(&members.front(), byrefint, py::cast(&self));
             })
        .def("__len__", [](const Scope& self) { return std::ranges::distance(self.members()); })
        .def(
            "__iter__",
            [](const Scope& self) {
                auto members = self.members();
                return py::make_iterator(members.begin(), members.end());
            },
            py::keep_alive<0, 1>());

    py::class_<AttributeSymbol, Symbol>(m, "AttributeSymbol")
        .def_property_readonly("value", &AttributeSymbol::getValue);

    py::class_<CompilationUnitSymbol, Symbol, Scope>(m, "CompilationUnitSymbol")
        .def_readonly("timeScale", &CompilationUnitSymbol::timeScale);

    py::class_<PackageSymbol, Symbol, Scope>(m, "PackageSymbol")
        .def_property_readonly("defaultNetType",
                               [](const PackageSymbol& self) { return &self.defaultNetType; })
        .def_readonly("timeScale", &PackageSymbol::timeScale)
        .def_readonly("defaultLifetime", &PackageSymbol::defaultLifetime)
        .def_readonly("exportDecls", &PackageSymbol::exportDecls)
        .def_readonly("hasExportAll", &PackageSymbol::hasExportAll)
        .def("findForImport", &PackageSymbol::findForImport, byrefint, "name"_a);

    py::class_<RootSymbol, Symbol, Scope>(m, "RootSymbol")
        .def_readonly("topInstances", &RootSymbol::topInstances)
        .def_readonly("compilationUnits", &RootSymbol::compilationUnits);

    py::class_<DefinitionSymbol, Symbol>(m, "DefinitionSymbol")
        .def_readonly("definitionKind", &DefinitionSymbol::definitionKind)
        .def_readonly("defaultLifetime", &DefinitionSymbol::defaultLifetime)
        .def_readonly("unconnectedDrive", &DefinitionSymbol::unconnectedDrive)
        .def_readonly("timeScale", &DefinitionSymbol::timeScale)
        .def_property_readonly("defaultNetType",
                               [](const DefinitionSymbol& self) { return &self.defaultNetType; })
        .def_property_readonly("instanceCount", &DefinitionSymbol::getInstanceCount)
        .def("getKindString", &DefinitionSymbol::getKindString)
        .def("getArticleKindString", &DefinitionSymbol::getArticleKindString)
        .def("__repr__", [](const DefinitionSymbol& self) {
            return fmt::format("DefinitionSymbol(\"{}\")", self.name);
        });

    py::class_<ValueSymbol, Symbol>(m, "ValueSymbol")
        .def_property_readonly("type", &ValueSymbol::getType)
        .def_property_readonly("initializer", &ValueSymbol::getInitializer)
        .def(
            "__iter__",
            [](const ValueSymbol& self) {
                auto drivers = self.drivers();
                return py::make_iterator(drivers.begin(), drivers.end());
            },
            py::keep_alive<0, 1>());

    py::class_<ValueDriver>(m, "ValueDriver")
        .def_readonly("prefixExpression", &ValueDriver::prefixExpression)
        .def_readonly("containingSymbol", &ValueDriver::containingSymbol)
        .def_readonly("procCallExpression", &ValueDriver::procCallExpression)
        .def_readonly("kind", &ValueDriver::kind)
        .def_readonly("flags", &ValueDriver::flags)
        .def_property_readonly("sourceRange", &ValueDriver::getSourceRange)
        .def_property_readonly("isInputPort", &ValueDriver::isInputPort)
        .def_property_readonly("isUnidirectionalPort", &ValueDriver::isUnidirectionalPort)
        .def_property_readonly("isClockVar", &ValueDriver::isClockVar)
        .def_property_readonly("isLocalVarFormalArg", &ValueDriver::isLocalVarFormalArg)
        .def_property_readonly("isInSingleDriverProcedure", &ValueDriver::isInSingleDriverProcedure)
        .def_property_readonly("isInSubroutine", &ValueDriver::isInSubroutine)
        .def_property_readonly("isInInitialBlock", &ValueDriver::isInInitialBlock);

    py::class_<EnumValueSymbol, ValueSymbol>(m, "EnumValueSymbol")
        .def_property_readonly("value",
                               [](const EnumValueSymbol& self) { return self.getValue(); });

    py::class_<ParameterSymbolBase>(m, "ParameterSymbolBase")
        .def_property_readonly("isLocalParam", &ParameterSymbolBase::isLocalParam)
        .def_property_readonly("isPortParam", &ParameterSymbolBase::isPortParam)
        .def_property_readonly("isBodyParam", &ParameterSymbolBase::isBodyParam);

    py::class_<ParameterSymbol, ValueSymbol, ParameterSymbolBase>(m, "ParameterSymbol")
        .def_property_readonly("value", [](const ParameterSymbol& self) { return self.getValue(); })
        .def_property_readonly("isOverridden", &ParameterSymbol::isOverridden);

    py::class_<TypeParameterSymbol, Symbol, ParameterSymbolBase>(m, "TypeParameterSymbol")
        .def_property_readonly("targetType",
                               [](const TypeParameterSymbol& self) { return &self.targetType; })
        .def_property_readonly("typeAlias",
                               [](const TypeParameterSymbol& self) { return &self.getTypeAlias(); })
        .def_property_readonly("isOverridden", &TypeParameterSymbol::isOverridden);

    py::class_<DefParamSymbol, Symbol>(m, "DefParamSymbol")
        .def_property_readonly("target",
                               [](const DefParamSymbol& self) { return self.getTarget(); })
        .def_property_readonly("initializer",
                               [](const DefParamSymbol& self) { return &self.getInitializer(); })
        .def_property_readonly("value", [](const DefParamSymbol& self) { return self.getValue(); });

    py::class_<SpecparamSymbol, ValueSymbol>(m, "SpecparamSymbol")
        .def_readonly("isPathPulse", &SpecparamSymbol::isPathPulse)
        .def_property_readonly("value", [](const SpecparamSymbol& self) { return self.getValue(); })
        .def_property_readonly("pulseRejectLimit",
                               [](const SpecparamSymbol& self) {
                                   return self.getPulseRejectLimit();
                               })
        .def_property_readonly("pulseErrorLimit",
                               [](const SpecparamSymbol& self) {
                                   return self.getPulseErrorLimit();
                               })
        .def_property_readonly("pathSource", &SpecparamSymbol::getPathSource)
        .def_property_readonly("pathDest", &SpecparamSymbol::getPathDest);

    py::enum_<VariableFlags>(m, "VariableFlags")
        .value("None_", VariableFlags::None)
        .value("Const", VariableFlags::Const)
        .value("CompilerGenerated", VariableFlags::CompilerGenerated)
        .value("ImmutableCoverageOption", VariableFlags::ImmutableCoverageOption)
        .value("CoverageSampleFormal", VariableFlags::CoverageSampleFormal)
        .value("CheckerFreeVariable", VariableFlags::CheckerFreeVariable)
        .value("RefStatic", VariableFlags::RefStatic);

    py::class_<VariableSymbol, ValueSymbol>(m, "VariableSymbol")
        .def_readonly("lifetime", &VariableSymbol::lifetime)
        .def_readonly("flags", &VariableSymbol::flags);

    py::class_<FormalArgumentSymbol, VariableSymbol>(m, "FormalArgumentSymbol")
        .def_readonly("direction", &FormalArgumentSymbol::direction)
        .def_property_readonly("defaultValue", &FormalArgumentSymbol::getDefaultValue);

    py::class_<FieldSymbol, VariableSymbol>(m, "FieldSymbol")
        .def_readonly("bitOffset", &FieldSymbol::bitOffset)
        .def_readonly("fieldIndex", &FieldSymbol::fieldIndex)
        .def_readonly("randMode", &FieldSymbol::randMode);

    py::class_<NetSymbol, ValueSymbol> netSymbol(m, "NetSymbol");
    netSymbol.def_readonly("expansionHint", &NetSymbol::expansionHint)
        .def_readonly("isImplicit", &NetSymbol::isImplicit)
        .def_property_readonly("netType", [](const NetSymbol& self) { return &self.netType; })
        .def_property_readonly("delay", &NetSymbol::getDelay)
        .def_property_readonly("chargeStrength", &NetSymbol::getChargeStrength)
        .def_property_readonly("driveStrength", &NetSymbol::getDriveStrength);

    py::enum_<NetSymbol::ExpansionHint>(netSymbol, "ExpansionHint")
        .value("None_", NetSymbol::None)
        .value("Vectored", NetSymbol::Vectored)
        .value("Scalared", NetSymbol::Scalared)
        .export_values();

    py::class_<TempVarSymbol, VariableSymbol>(m, "TempVarSymbol");
    py::class_<IteratorSymbol, TempVarSymbol>(m, "IteratorSymbol");
    py::class_<PatternVarSymbol, TempVarSymbol>(m, "PatternVarSymbol");
    py::class_<LocalAssertionVarSymbol, VariableSymbol>(m, "LocalAssertionVarSymbol");

    py::class_<ClockingSkew>(m, "ClockingSkew")
        .def_readonly("edge", &ClockingSkew::edge)
        .def_readonly("delay", &ClockingSkew::delay)
        .def_property_readonly("hasValue", &ClockingSkew::hasValue);

    py::class_<ClockVarSymbol, VariableSymbol>(m, "ClockVarSymbol")
        .def_readonly("direction", &ClockVarSymbol::direction)
        .def_readonly("inputSkew", &ClockVarSymbol::inputSkew)
        .def_readonly("outputSkew", &ClockVarSymbol::outputSkew);

    py::class_<ClassPropertySymbol, VariableSymbol>(m, "ClassPropertySymbol")
        .def_readonly("visibility", &ClassPropertySymbol::visibility)
        .def_readonly("randMode", &ClassPropertySymbol::randMode);

    py::enum_<MethodFlags>(m, "MethodFlags")
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

    py::class_<SubroutineSymbol, Symbol, Scope>(m, "SubroutineSymbol")
        .def_readonly("defaultLifetime", &SubroutineSymbol::defaultLifetime)
        .def_readonly("subroutineKind", &SubroutineSymbol::subroutineKind)
        .def_readonly("visibility", &SubroutineSymbol::visibility)
        .def_readonly("flags", &SubroutineSymbol::flags)
        .def_property_readonly("arguments", &SubroutineSymbol::getArguments)
        .def_property_readonly("body", &SubroutineSymbol::getBody)
        .def_property_readonly("returnType", &SubroutineSymbol::getReturnType)
        .def_property_readonly("override", &SubroutineSymbol::getOverride)
        .def_property_readonly("prototype", &SubroutineSymbol::getPrototype)
        .def_property_readonly("isVirtual", &SubroutineSymbol::isVirtual);

    py::class_<MethodPrototypeSymbol, Symbol, Scope> methodProto(m, "MethodPrototypeSymbol");
    methodProto.def_readonly("subroutineKind", &MethodPrototypeSymbol::subroutineKind)
        .def_readonly("visibility", &MethodPrototypeSymbol::visibility)
        .def_readonly("flags", &MethodPrototypeSymbol::flags)
        .def_property_readonly("arguments", &MethodPrototypeSymbol::getArguments)
        .def_property_readonly("returnType", &MethodPrototypeSymbol::getReturnType)
        .def_property_readonly("override", &MethodPrototypeSymbol::getOverride)
        .def_property_readonly("subroutine", &MethodPrototypeSymbol::getSubroutine)
        .def_property_readonly("isVirtual", &MethodPrototypeSymbol::isVirtual)
        .def_property_readonly("firstExternImpl", &MethodPrototypeSymbol::getFirstExternImpl);

    py::class_<MethodPrototypeSymbol::ExternImpl>(methodProto, "ExternImpl")
        .def_readonly("impl", &MethodPrototypeSymbol::ExternImpl::impl)
        .def_property_readonly("nextImpl", &MethodPrototypeSymbol::ExternImpl::getNextImpl);

    py::class_<PortSymbol, Symbol>(m, "PortSymbol")
        .def_readonly("internalSymbol", &PortSymbol::internalSymbol)
        .def_readonly("externalLoc", &PortSymbol::externalLoc)
        .def_readonly("direction", &PortSymbol::direction)
        .def_readonly("isNullPort", &PortSymbol::isNullPort)
        .def_readonly("isAnsiPort", &PortSymbol::isAnsiPort)
        .def_property_readonly("type", &PortSymbol::getType)
        .def_property_readonly("initializer", &PortSymbol::getInitializer)
        .def_property_readonly("internalExpr", &PortSymbol::getInternalExpr)
        .def_property_readonly("isNetPort", &PortSymbol::isNetPort);

    py::class_<MultiPortSymbol, Symbol>(m, "MultiPortSymbol")
        .def_readonly("ports", &MultiPortSymbol::ports)
        .def_readonly("direction", &MultiPortSymbol::direction)
        .def_readonly("isNullPort", &MultiPortSymbol::isNullPort)
        .def_property_readonly("type", &MultiPortSymbol::getType)
        .def_property_readonly("initializer", &MultiPortSymbol::getInitializer);

    py::class_<InterfacePortSymbol, Symbol>(m, "InterfacePortSymbol")
        .def_readonly("interfaceDef", &InterfacePortSymbol::interfaceDef)
        .def_readonly("modport", &InterfacePortSymbol::modport)
        .def_readonly("isGeneric", &InterfacePortSymbol::isGeneric)
        .def_property_readonly("declaredRange", &InterfacePortSymbol::getDeclaredRange)
        .def_property_readonly("connection", &InterfacePortSymbol::getConnection)
        .def_property_readonly("isInvalid", &InterfacePortSymbol::isInvalid);

    py::class_<PortConnection>(m, "PortConnection")
        .def_property_readonly("ifaceConn", &PortConnection::getIfaceConn)
        .def_property_readonly("expression", &PortConnection::getExpression)
        .def_property_readonly("port", [](const PortConnection& self) { return &self.port; });

    py::class_<InstanceSymbolBase, Symbol>(m, "InstanceSymbolBase")
        .def_readonly("arrayPath", &InstanceSymbolBase::arrayPath)
        .def_property_readonly("arrayName", &InstanceSymbolBase::getArrayName);

    py::class_<InstanceSymbol, InstanceSymbolBase>(m, "InstanceSymbol")
        .def_property_readonly("definition", &InstanceSymbol::getDefinition)
        .def_property_readonly("isModule", &InstanceSymbol::isModule)
        .def_property_readonly("isInterface", &InstanceSymbol::isInterface)
        .def_property_readonly("portConnections", &InstanceSymbol::getPortConnections)
        .def_property_readonly("body", [](const InstanceSymbol& self) { return &self.body; })
        .def("getPortConnection",
             py::overload_cast<const PortSymbol&>(&InstanceSymbol::getPortConnection, py::const_),
             byrefint, "port"_a)
        .def("getPortConnection",
             py::overload_cast<const MultiPortSymbol&>(&InstanceSymbol::getPortConnection,
                                                       py::const_),
             byrefint, "port"_a)
        .def("getPortConnection",
             py::overload_cast<const InterfacePortSymbol&>(&InstanceSymbol::getPortConnection,
                                                           py::const_),
             byrefint, "port"_a);

    py::class_<InstanceBodySymbol, Symbol, Scope>(m, "InstanceBodySymbol")
        .def_readonly("parentInstance", &InstanceBodySymbol::parentInstance)
        .def_property_readonly("parameters", &InstanceBodySymbol::getParameters)
        .def_property_readonly("portList", &InstanceBodySymbol::getPortList)
        .def_property_readonly("definition", &InstanceBodySymbol::getDefinition)
        .def("findPort", &InstanceBodySymbol::findPort, byrefint, "portName"_a)
        .def("hasSameType", &InstanceBodySymbol::hasSameType, "other"_a);

    py::class_<InstanceArraySymbol, Symbol, Scope>(m, "InstanceArraySymbol")
        .def_readonly("elements", &InstanceArraySymbol::elements)
        .def_readonly("range", &InstanceArraySymbol::range)
        .def_property_readonly("arrayName", &InstanceArraySymbol::getArrayName);

    py::class_<UninstantiatedDefSymbol, Symbol>(m, "UninstantiatedDefSymbol")
        .def_readonly("definitionName", &UninstantiatedDefSymbol::definitionName)
        .def_readonly("paramExpressions", &UninstantiatedDefSymbol::paramExpressions)
        .def_property_readonly("portConnections", &UninstantiatedDefSymbol::getPortConnections)
        .def_property_readonly("portNames", &UninstantiatedDefSymbol::getPortNames)
        .def_property_readonly("isChecker", &UninstantiatedDefSymbol::isChecker);

    py::class_<PrimitiveInstanceSymbol, InstanceSymbolBase>(m, "PrimitiveInstanceSymbol")
        .def_property_readonly("primitiveType",
                               [](const PrimitiveInstanceSymbol& self) {
                                   return &self.primitiveType;
                               })
        .def_property_readonly("portConnections", &PrimitiveInstanceSymbol::getPortConnections)
        .def_property_readonly("delay", &PrimitiveInstanceSymbol::getDelay)
        .def_property_readonly("driveStrength", &PrimitiveInstanceSymbol::getDriveStrength);

    py::class_<CheckerInstanceSymbol, InstanceSymbolBase> checkerInst(m, "CheckerInstanceSymbol");
    checkerInst
        .def_property_readonly("body", [](const CheckerInstanceSymbol& self) { return &self.body; })
        .def_property_readonly("portConnections", &CheckerInstanceSymbol::getPortConnections);

    py::class_<CheckerInstanceSymbol::Connection>(checkerInst, "Connection")
        .def_property_readonly(
            "formal", [](const CheckerInstanceSymbol::Connection& self) { return &self.formal; })
        .def_property_readonly("outputInitialExpr",
                               &CheckerInstanceSymbol::Connection::getOutputInitialExpr)
        .def_readonly("actual", &CheckerInstanceSymbol::Connection::actual)
        .def_readonly("attributes", &CheckerInstanceSymbol::Connection::attributes);

    py::class_<CheckerInstanceBodySymbol, Symbol, Scope>(m, "CheckerInstanceBodySymbol")
        .def_readonly("parentInstance", &CheckerInstanceBodySymbol::parentInstance)
        .def_property_readonly("checker",
                               [](const CheckerInstanceBodySymbol& self) { return &self.checker; });

    py::class_<StatementBlockSymbol, Symbol, Scope>(m, "StatementBlockSymbol")
        .def_readonly("blockKind", &StatementBlockSymbol::blockKind)
        .def_readonly("defaultLifetime", &StatementBlockSymbol::defaultLifetime);

    py::class_<ProceduralBlockSymbol, Symbol>(m, "ProceduralBlockSymbol")
        .def_readonly("procedureKind", &ProceduralBlockSymbol::procedureKind)
        .def_property_readonly("isSingleDriverBlock", &ProceduralBlockSymbol::isSingleDriverBlock)
        .def_property_readonly("body", &ProceduralBlockSymbol::getBody);

    py::class_<GenerateBlockSymbol, Symbol, Scope>(m, "GenerateBlockSymbol")
        .def_readonly("constructIndex", &GenerateBlockSymbol::constructIndex)
        .def_readonly("isUninstantiated", &GenerateBlockSymbol::isUninstantiated)
        .def_readonly("arrayIndex", &GenerateBlockSymbol::arrayIndex)
        .def_property_readonly("externalName", &GenerateBlockSymbol::getExternalName);

    py::class_<GenerateBlockArraySymbol, Symbol, Scope>(m, "GenerateBlockArraySymbol")
        .def_readonly("constructIndex", &GenerateBlockArraySymbol::constructIndex)
        .def_readonly("entries", &GenerateBlockArraySymbol::entries)
        .def_readonly("valid", &GenerateBlockArraySymbol::valid)
        .def_property_readonly("externalName", &GenerateBlockArraySymbol::getExternalName);

    py::class_<EmptyMemberSymbol, Symbol>(m, "EmptyMemberSymbol");
    py::class_<GenvarSymbol, Symbol>(m, "GenvarSymbol");
    py::class_<SpecifyBlockSymbol, Symbol, Scope>(m, "SpecifyBlockSymbol");
    py::class_<AnonymousProgramSymbol, Symbol, Scope>(m, "AnonymousProgramSymbol");

    py::class_<NetAliasSymbol, Symbol>(m, "NetAliasSymbol")
        .def_property_readonly("netReferences", &NetAliasSymbol::getNetReferences);

    py::class_<TransparentMemberSymbol, Symbol>(m, "TransparentMemberSymbol")
        .def_property_readonly("wrapped",
                               [](const TransparentMemberSymbol& self) { return &self.wrapped; });

    py::class_<ExplicitImportSymbol, Symbol>(m, "ExplicitImportSymbol")
        .def_readonly("packageName", &ExplicitImportSymbol::packageName)
        .def_readonly("importName", &ExplicitImportSymbol::importName)
        .def_readonly("isFromExport", &ExplicitImportSymbol::isFromExport)
        .def_property_readonly("package", &ExplicitImportSymbol::package)
        .def_property_readonly("importedSymbol", &ExplicitImportSymbol::importedSymbol);

    py::class_<WildcardImportSymbol, Symbol>(m, "WildcardImportSymbol")
        .def_readonly("packageName", &WildcardImportSymbol::packageName)
        .def_readonly("isFromExport", &WildcardImportSymbol::isFromExport)
        .def_property_readonly("package", &WildcardImportSymbol::getPackage);

    py::class_<ModportPortSymbol, ValueSymbol>(m, "ModportPortSymbol")
        .def_readonly("direction", &ModportPortSymbol::direction)
        .def_readonly("internalSymbol", &ModportPortSymbol::internalSymbol)
        .def_readonly("explicitConnection", &ModportPortSymbol::explicitConnection);

    py::class_<ModportClockingSymbol, Symbol>(m, "ModportClockingSymbol")
        .def_readonly("target", &ModportClockingSymbol::target);

    py::class_<ModportSymbol, Symbol, Scope>(m, "ModportSymbol")
        .def_readonly("hasExports", &ModportSymbol::hasExports);

    py::class_<ContinuousAssignSymbol, Symbol>(m, "ContinuousAssignSymbol")
        .def_property_readonly("assignment", &ContinuousAssignSymbol::getAssignment)
        .def_property_readonly("delay", &ContinuousAssignSymbol::getDelay)
        .def_property_readonly("driveStrength", &ContinuousAssignSymbol::getDriveStrength);

    py::class_<ElabSystemTaskSymbol, Symbol>(m, "ElabSystemTaskSymbol")
        .def_readonly("taskKind", &ElabSystemTaskSymbol::taskKind)
        .def_property_readonly("message", &ElabSystemTaskSymbol::getMessage)
        .def_property_readonly("assertCondition", &ElabSystemTaskSymbol::getAssertCondition);

    py::class_<PrimitivePortSymbol, ValueSymbol>(m, "PrimitivePortSymbol")
        .def_readonly("direction", &PrimitivePortSymbol::direction);

    py::class_<PrimitiveSymbol, Symbol, Scope> primitiveSym(m, "PrimitiveSymbol");
    primitiveSym.def_readonly("ports", &PrimitiveSymbol::ports)
        .def_readonly("initVal", &PrimitiveSymbol::initVal)
        .def_readonly("primitiveKind", &PrimitiveSymbol::primitiveKind)
        .def_readonly("isSequential", &PrimitiveSymbol::isSequential)
        .def_readonly("table", &PrimitiveSymbol::table);

    py::enum_<PrimitiveSymbol::PrimitiveKind>(primitiveSym, "PrimitiveKind")
        .value("UserDefined", PrimitiveSymbol::PrimitiveKind::UserDefined)
        .value("Fixed", PrimitiveSymbol::PrimitiveKind::Fixed)
        .value("NInput", PrimitiveSymbol::PrimitiveKind::NInput)
        .value("NOutput", PrimitiveSymbol::PrimitiveKind::NOutput)
        .export_values();

    py::class_<PrimitiveSymbol::TableEntry>(primitiveSym, "TableEntry")
        .def_readonly("inputs", &PrimitiveSymbol::TableEntry::inputs)
        .def_readonly("state", &PrimitiveSymbol::TableEntry::state)
        .def_readonly("output", &PrimitiveSymbol::TableEntry::output);

    py::class_<AssertionPortSymbol, Symbol>(m, "AssertionPortSymbol")
        .def_readonly("direction", &AssertionPortSymbol::direction)
        .def_property_readonly("isLocalVar", &AssertionPortSymbol::isLocalVar)
        .def_property_readonly("type", [](const AssertionPortSymbol& self) {
            return &self.declaredType.getType();
        });

    py::class_<SequenceSymbol, Symbol, Scope>(m, "SequenceSymbol")
        .def_readonly("ports", &SequenceSymbol::ports);

    py::class_<PropertySymbol, Symbol, Scope>(m, "PropertySymbol")
        .def_readonly("ports", &PropertySymbol::ports);

    py::class_<LetDeclSymbol, Symbol, Scope>(m, "LetDeclSymbol")
        .def_readonly("ports", &LetDeclSymbol::ports);

    py::class_<CheckerSymbol, Symbol, Scope>(m, "CheckerSymbol")
        .def_readonly("ports", &CheckerSymbol::ports);

    py::class_<ClockingBlockSymbol, Symbol, Scope>(m, "ClockingBlockSymbol")
        .def_property_readonly("event", &ClockingBlockSymbol::getEvent)
        .def_property_readonly("defaultInputSkew", &ClockingBlockSymbol::getDefaultInputSkew)
        .def_property_readonly("defaultOutputSkew", &ClockingBlockSymbol::getDefaultOutputSkew);

    py::class_<RandSeqProductionSymbol, Symbol, Scope> randSeq(m, "RandSeqProductionSymbol");
    randSeq.def_readonly("arguments", &RandSeqProductionSymbol::arguments)
        .def_property_readonly("rules", &RandSeqProductionSymbol::getRules)
        .def_property_readonly("returnType", &RandSeqProductionSymbol::getReturnType);

    py::enum_<RandSeqProductionSymbol::ProdKind>(randSeq, "ProdKind")
        .value("Item", RandSeqProductionSymbol::ProdKind::Item)
        .value("CodeBlock", RandSeqProductionSymbol::ProdKind::CodeBlock)
        .value("IfElse", RandSeqProductionSymbol::ProdKind::IfElse)
        .value("Repeat", RandSeqProductionSymbol::ProdKind::Repeat)
        .value("Case", RandSeqProductionSymbol::ProdKind::Case);

    py::class_<RandSeqProductionSymbol::ProdBase>(randSeq, "ProdBase")
        .def_readonly("kind", &RandSeqProductionSymbol::ProdBase::kind);

    py::class_<RandSeqProductionSymbol::ProdItem, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                     "ProdItem")
        .def_readonly("target", &RandSeqProductionSymbol::ProdItem::target)
        .def_readonly("args", &RandSeqProductionSymbol::ProdItem::args);

    py::class_<RandSeqProductionSymbol::CodeBlockProd, RandSeqProductionSymbol::ProdBase>(
        randSeq, "CodeBlockProd")
        .def_readonly("block", &RandSeqProductionSymbol::CodeBlockProd::block);

    py::class_<RandSeqProductionSymbol::IfElseProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                       "IfElseProd")
        .def_readonly("expr", &RandSeqProductionSymbol::IfElseProd::expr)
        .def_readonly("ifItem", &RandSeqProductionSymbol::IfElseProd::ifItem)
        .def_readonly("elseItem", &RandSeqProductionSymbol::IfElseProd::elseItem);

    py::class_<RandSeqProductionSymbol::RepeatProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                       "RepeatProd")
        .def_readonly("expr", &RandSeqProductionSymbol::RepeatProd::expr)
        .def_readonly("item", &RandSeqProductionSymbol::RepeatProd::item);

    py::class_<RandSeqProductionSymbol::CaseItem>(randSeq, "CaseItem")
        .def_readonly("expressions", &RandSeqProductionSymbol::CaseItem::expressions)
        .def_readonly("item", &RandSeqProductionSymbol::CaseItem::item);

    py::class_<RandSeqProductionSymbol::CaseProd, RandSeqProductionSymbol::ProdBase>(randSeq,
                                                                                     "CaseProd")
        .def_readonly("expr", &RandSeqProductionSymbol::CaseProd::expr)
        .def_readonly("items", &RandSeqProductionSymbol::CaseProd::items)
        .def_readonly("defaultItem", &RandSeqProductionSymbol::CaseProd::defaultItem);

    py::class_<RandSeqProductionSymbol::Rule>(randSeq, "Rule")
        .def_readonly("ruleBlock", &RandSeqProductionSymbol::Rule::ruleBlock)
        .def_readonly("prods", &RandSeqProductionSymbol::Rule::prods)
        .def_readonly("weightExpr", &RandSeqProductionSymbol::Rule::weightExpr)
        .def_readonly("randJoinExpr", &RandSeqProductionSymbol::Rule::randJoinExpr)
        .def_readonly("codeBlock", &RandSeqProductionSymbol::Rule::codeBlock)
        .def_readonly("isRandJoin", &RandSeqProductionSymbol::Rule::isRandJoin);

    py::class_<TimingPathSymbol, Symbol> timingPath(m, "TimingPathSymbol");
    timingPath.def_readonly("connectionKind", &TimingPathSymbol::connectionKind)
        .def_readonly("polarity", &TimingPathSymbol::polarity)
        .def_readonly("edgePolarity", &TimingPathSymbol::edgePolarity)
        .def_readonly("edgeIdentifier", &TimingPathSymbol::edgeIdentifier)
        .def_readonly("isStateDependent", &TimingPathSymbol::isStateDependent)
        .def_property_readonly("edgeSourceExpr", &TimingPathSymbol::getEdgeSourceExpr)
        .def_property_readonly("conditionExpr", &TimingPathSymbol::getConditionExpr)
        .def_property_readonly("inputs", &TimingPathSymbol::getInputs)
        .def_property_readonly("outputs", &TimingPathSymbol::getOutputs)
        .def_property_readonly("delays", &TimingPathSymbol::getDelays);

    py::enum_<TimingPathSymbol::ConnectionKind>(timingPath, "ConnectionKind")
        .value("Full", TimingPathSymbol::ConnectionKind::Full)
        .value("Parallel", TimingPathSymbol::ConnectionKind::Parallel);

    py::enum_<TimingPathSymbol::Polarity>(timingPath, "Polarity")
        .value("Unknown", TimingPathSymbol::Polarity::Unknown)
        .value("Positive", TimingPathSymbol::Polarity::Positive)
        .value("Negative", TimingPathSymbol::Polarity::Negative);

    py::class_<PulseStyleSymbol, Symbol>(m, "PulseStyleSymbol")
        .def_readonly("pulseStyleKind", &PulseStyleSymbol::pulseStyleKind)
        .def_property_readonly("terminals", &PulseStyleSymbol::getTerminals);

    py::class_<SystemTimingCheckSymbol, Symbol> timingCheck(m, "SystemTimingCheckSymbol");
    timingCheck.def_readonly("timingCheckKind", &SystemTimingCheckSymbol::timingCheckKind)
        .def_property_readonly("arguments", &SystemTimingCheckSymbol::getArguments);

    py::class_<SystemTimingCheckSymbol::Arg>(timingCheck, "Arg")
        .def_readonly("expr", &SystemTimingCheckSymbol::Arg::expr)
        .def_readonly("condition", &SystemTimingCheckSymbol::Arg::condition)
        .def_readonly("edge", &SystemTimingCheckSymbol::Arg::edge)
        .def_readonly("edgeDescriptors", &SystemTimingCheckSymbol::Arg::edgeDescriptors);

    py::class_<CoverageOptionSetter>(m, "CoverageOptionSetter")
        .def_property_readonly("isTypeOption", &CoverageOptionSetter::isTypeOption)
        .def_property_readonly("name", &CoverageOptionSetter::getName)
        .def_property_readonly("expression", &CoverageOptionSetter::getExpression);

    py::class_<CovergroupBodySymbol, Symbol, Scope>(m, "CovergroupBodySymbol")
        .def_readonly("options", &CovergroupBodySymbol::options);

    py::class_<CoverageBinSymbol, Symbol> coverageBinSym(m, "CoverageBinSymbol");
    coverageBinSym.def_readonly("binsKind", &CoverageBinSymbol::binsKind)
        .def_readonly("isArray", &CoverageBinSymbol::isArray)
        .def_readonly("isWildcard", &CoverageBinSymbol::isWildcard)
        .def_readonly("isDefault", &CoverageBinSymbol::isDefault)
        .def_readonly("isDefaultSequence", &CoverageBinSymbol::isDefaultSequence)
        .def_property_readonly("iffExpr", &CoverageBinSymbol::getIffExpr)
        .def_property_readonly("numberOfBinsExpr", &CoverageBinSymbol::getNumberOfBinsExpr)
        .def_property_readonly("setCoverageExpr", &CoverageBinSymbol::getSetCoverageExpr)
        .def_property_readonly("withExpr", &CoverageBinSymbol::getWithExpr)
        .def_property_readonly("crossSelectExpr", &CoverageBinSymbol::getCrossSelectExpr)
        .def_property_readonly("values", &CoverageBinSymbol::getValues);

    py::class_<CoverageBinSymbol::TransRangeList> transRangeList(coverageBinSym, "TransRangeList");
    transRangeList.def_readonly("items", &CoverageBinSymbol::TransRangeList::items)
        .def_readonly("repeatFrom", &CoverageBinSymbol::TransRangeList::repeatFrom)
        .def_readonly("repeatTo", &CoverageBinSymbol::TransRangeList::repeatTo)
        .def_readonly("repeatKind", &CoverageBinSymbol::TransRangeList::repeatKind);

    py::enum_<CoverageBinSymbol::TransRangeList::RepeatKind>(transRangeList, "RepeatKind")
        .value("None_", CoverageBinSymbol::TransRangeList::None)
        .value("Consecutive", CoverageBinSymbol::TransRangeList::Consecutive)
        .value("Nonconsecutive", CoverageBinSymbol::TransRangeList::Nonconsecutive)
        .value("GoTo", CoverageBinSymbol::TransRangeList::GoTo)
        .export_values();

    py::enum_<CoverageBinSymbol::BinKind>(coverageBinSym, "BinKind")
        .value("Bins", CoverageBinSymbol::Bins)
        .value("IllegalBins", CoverageBinSymbol::IllegalBins)
        .value("IgnoreBins", CoverageBinSymbol::IgnoreBins)
        .export_values();

    py::class_<CoverpointSymbol, Symbol, Scope>(m, "CoverpointSymbol")
        .def_readonly("options", &CoverpointSymbol::options)
        .def_property_readonly("type", &CoverpointSymbol::getType)
        .def_property_readonly("coverageExpr", &CoverpointSymbol::getCoverageExpr)
        .def_property_readonly("iffExpr", &CoverpointSymbol::getIffExpr);

    py::class_<CoverCrossBodySymbol, Symbol, Scope>(m, "CoverCrossBodySymbol")
        .def_readonly("crossQueueType", &CoverCrossBodySymbol::crossQueueType);

    py::class_<CoverCrossSymbol, Symbol, Scope>(m, "CoverCrossSymbol")
        .def_readonly("options", &CoverCrossSymbol::options)
        .def_readonly("targets", &CoverCrossSymbol::targets)
        .def_property_readonly("iffExpr", &CoverCrossSymbol::getIffExpr);

    py::class_<ConfigBlockSymbol, Symbol, Scope>(m, "ConfigBlockSymbol");
}

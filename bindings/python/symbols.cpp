//------------------------------------------------------------------------------
// symbols.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/DeclaredType.h"
#include "slang/types/NetType.h"

void registerSymbols(py::module_& m) {
    EXPOSE_ENUM(m, SymbolKind);

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
             py::overload_cast<const Symbol&>(&Symbol::isDeclaredBefore, py::const_))
        .def("isDeclaredBefore",
             py::overload_cast<LookupLocation>(&Symbol::isDeclaredBefore, py::const_))
        .def("__repr__", [](const Symbol& self) {
            return fmt::format("Symbol(SymbolKind.{}, \"{}\")", toString(self.kind), self.name);
        });

    py::class_<Scope>(m, "Scope")
        .def_property_readonly("compilation", &Scope::getCompilation)
        .def_property_readonly("defaultNetType", &Scope::getDefaultNetType)
        .def_property_readonly("timeScale", &Scope::getTimeScale)
        .def_property_readonly("isProceduralContext", &Scope::isProceduralContext)
        .def_property_readonly("containingInstance", &Scope::getContainingInstance)
        .def_property_readonly("isUninstantiated", &Scope::isUninstantiated)
        .def_property_readonly("containingInstance", &Scope::getContainingInstance)
        .def(
            "find", [](const Scope& self, string_view arg) { return self.find(arg); }, byrefint)
        // TODO:
        /*.def(
            "lookupName",
            [](const Scope& self, string_view arg, LookupLocation location,
               bitmask<LookupFlags> flags) { return self.lookupName(arg, location, flags); },
            "name"_a, "location"_a = LookupLocation::max, "flags"_a = LookupFlags::None, byrefint)*/
        .def("__len__", [](const Scope& self) { return self.members().size(); })
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
        .def("findForImport", &PackageSymbol::findForImport, byrefint);

    py::class_<RootSymbol, Symbol, Scope>(m, "RootSymbol")
        .def_readonly("topInstances", &RootSymbol::topInstances)
        .def_readonly("compilationUnits", &RootSymbol::compilationUnits);
}

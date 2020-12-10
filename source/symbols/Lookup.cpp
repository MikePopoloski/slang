//------------------------------------------------------------------------------
// Lookup.cpp
// Symbol lookup logic
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/Lookup.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/compilation/Definition.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"
#include "slang/util/String.h"

namespace slang {

const LookupLocation LookupLocation::max{ nullptr, UINT_MAX };
const LookupLocation LookupLocation::min{ nullptr, 0 };

LookupLocation LookupLocation::before(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex());
}

LookupLocation LookupLocation::after(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex() + 1);
}

bool LookupLocation::operator<(const LookupLocation& other) const {
    ASSERT(scope == other.scope || !scope || !other.scope);
    return index < other.index;
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceLocation location) {
    return diagnostics.add(scope.asSymbol(), code, location);
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(scope.asSymbol(), code, sourceRange);
}

bool LookupResult::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    return !diagnostics.empty() || (!found && wasImported);
}

void LookupResult::clear() {
    found = nullptr;
    systemSubroutine = nullptr;
    wasImported = false;
    isHierarchical = false;
    sawBadImport = false;
    fromTypeParam = false;
    fromForwardTypedef = false;
    selectors.clear();
    diagnostics.clear();
}

void LookupResult::copyFrom(const LookupResult& other) {
    found = other.found;
    systemSubroutine = other.systemSubroutine;
    wasImported = other.wasImported;
    isHierarchical = other.isHierarchical;
    sawBadImport = other.sawBadImport;
    fromTypeParam = other.fromTypeParam;
    fromForwardTypedef = other.fromForwardTypedef;

    selectors.clear();
    selectors.appendRange(other.selectors);

    diagnostics.clear();
    diagnostics.appendRange(other.diagnostics);
}

void LookupResult::reportErrors(const BindContext& context) {
    if (!hasError())
        return;

    // If we failed to find the symbol because of restrictions on hierarchical names
    // inside constant expressions (which we know if evalContext is set) then issue
    // a backtrace to give the user a bit more context.
    if (!found && isHierarchical && context.evalContext) {
        Diagnostic& first = diagnostics.front();
        context.evalContext->reportStack(first);
    }

    context.getCompilation().addDiagnostics(diagnostics);
}

namespace {

struct NamePlusLoc {
    const NameSyntax* name;
    SourceLocation dotLocation;
};

struct NameComponents {
    Token id;
    const SyntaxList<ElementSelectSyntax>* selectors = nullptr;
    const ParameterValueAssignmentSyntax* paramAssignments = nullptr;

    NameComponents() = default;
    NameComponents(const NameSyntax& name) {
        switch (name.kind) {
            case SyntaxKind::IdentifierName:
                id = name.as<IdentifierNameSyntax>().identifier;
                break;
            case SyntaxKind::SystemName:
                id = name.as<SystemNameSyntax>().systemIdentifier;
                break;
            case SyntaxKind::IdentifierSelectName: {
                auto& idSelect = name.as<IdentifierSelectNameSyntax>();
                id = idSelect.identifier;
                selectors = &idSelect.selectors;
                break;
            }
            case SyntaxKind::ClassName: {
                auto& cn = name.as<ClassNameSyntax>();
                id = cn.identifier;
                paramAssignments = cn.parameters;
                break;
            }
            case SyntaxKind::UnitScope:
            case SyntaxKind::RootScope:
            case SyntaxKind::LocalScope:
            case SyntaxKind::ThisHandle:
            case SyntaxKind::SuperHandle:
            case SyntaxKind::ArrayUniqueMethod:
            case SyntaxKind::ArrayAndMethod:
            case SyntaxKind::ArrayOrMethod:
            case SyntaxKind::ArrayXorMethod:
            case SyntaxKind::ConstructorName:
                id = name.as<KeywordNameSyntax>().keyword;
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    SourceRange range() const { return id.range(); }
    string_view text() const { return id.valueText(); }
};

const Symbol* unwrapTypeParam(const Symbol* symbol) {
    if (symbol->kind == SymbolKind::TypeParameter) {
        auto result = &symbol->as<TypeParameterSymbol>().targetType.getType();
        if (result->isError())
            return nullptr;

        return result;
    }
    return symbol;
}

bool isClassType(const Symbol& symbol) {
    if (symbol.isType())
        return symbol.as<Type>().isClass();

    return symbol.kind == SymbolKind::GenericClassDef;
}

const NameSyntax* splitScopedName(const ScopedNameSyntax& syntax,
                                  SmallVector<NamePlusLoc>& nameParts, int& colonParts) {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    const ScopedNameSyntax* scoped = &syntax;
    while (true) {
        nameParts.append({ scoped->right, scoped->separator.location() });
        if (scoped->separator.kind == TokenKind::Dot)
            colonParts = 0;
        else
            colonParts++;

        if (scoped->left->kind != SyntaxKind::ScopedName)
            break;

        scoped = &scoped->left->as<ScopedNameSyntax>();
    }
    return scoped->left;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupDownward(span<const NamePlusLoc> nameParts, NameComponents name,
                    const BindContext& context, LookupResult& result, bitmask<LookupFlags> flags) {
    const Symbol* symbol = std::exchange(result.found, nullptr);
    ASSERT(symbol);

    // Helper function to check whether class parameter assignments have been
    // incorrectly supplied for a non-class symbol.
    auto checkClassParams = [&](NameComponents& nc) {
        if (symbol && symbol->kind != SymbolKind::GenericClassDef && nc.paramAssignments) {
            auto& diag = result.addDiag(context.scope, diag::NotAGenericClass,
                                        nc.paramAssignments->getFirstToken().location());
            diag << nc.range();
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return false;
        }
        return true;
    };

    // Loop through each dotted name component and try to find it in the preceeding scope.
    for (auto it = nameParts.rbegin(); it != nameParts.rend(); it++) {
        if (!checkClassParams(name))
            return false;

        // If we found a value, the remaining dots are member access expressions.
        if (symbol->isValue()) {
            if (name.selectors)
                result.selectors.appendRange(*name.selectors);

            for (; it != nameParts.rend(); it++) {
                NameComponents memberName = *it->name;
                result.selectors.append(LookupResult::MemberSelector{
                    memberName.text(), it->dotLocation, memberName.range() });

                if (memberName.selectors)
                    result.selectors.appendRange(*memberName.selectors);

                if (!checkClassParams(memberName))
                    return false;
            }

            // Break out to return the symbol.
            name.selectors = nullptr;
            break;
        }

        // This is a hierarchical lookup unless it's the first component in the path and the
        // current scope is either an interface port or a package, or it's an instance that
        // is in the same scope as the lookup.
        result.isHierarchical = true;
        if (it == nameParts.rbegin()) {
            if (symbol->kind == SymbolKind::InstanceArray || symbol->kind == SymbolKind::Instance) {
                result.isHierarchical = symbol->getParentScope() != &context.scope;
            }
            else {
                result.isHierarchical = symbol->kind != SymbolKind::InterfacePort &&
                                        symbol->kind != SymbolKind::Package &&
                                        symbol->kind != SymbolKind::CompilationUnit;
            }
        }

        string_view modportName;
        if (symbol->kind == SymbolKind::InterfacePort) {
            auto& ifacePort = symbol->as<InterfacePortSymbol>();
            symbol = ifacePort.getConnection();
            if (!symbol)
                return false;

            modportName = ifacePort.modport;
        }

        if ((!symbol->isScope() && symbol->kind != SymbolKind::Instance) || symbol->isType()) {
            // If we found an unknown module, exit silently. An appropriate error was
            // already issued, so no need to pile on.
            if (symbol->kind == SymbolKind::UnknownModule)
                return false;

            symbol = unwrapTypeParam(symbol);
            if (!symbol)
                return false;

            bool isType = symbol->isType() || isClassType(*symbol);
            auto code = isType ? diag::DotOnType : diag::NotAHierarchicalScope;
            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << name.range();
            diag << it->name->sourceRange();

            if (!isType)
                diag << name.text();

            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return true;
        }

        if (result.isHierarchical && (flags & LookupFlags::Constant) != 0) {
            auto& diag = result.addDiag(context.scope, diag::HierarchicalNotAllowedInConstant,
                                        it->dotLocation);
            diag << name.range();
            return false;
        }

        if (name.selectors) {
            symbol = Lookup::selectChild(*symbol, *name.selectors, context, result);
            if (!symbol)
                return false;
        }

        if (symbol->kind == SymbolKind::Instance)
            symbol = &symbol->as<InstanceSymbol>().body;

        // If there is a modport name restricting our lookup, translate to that
        // modport's scope now.
        if (!modportName.empty()) {
            symbol = symbol->as<Scope>().find(modportName);
            if (!symbol)
                return false;
        }

        name = *it->name;
        if (name.text().empty())
            return false;

        auto& scope = symbol->as<Scope>();
        symbol = scope.find(name.text());
        if (!symbol) {
            // If we did the lookup in a modport, check to see if the symbol actually
            // exists in the parent interface.
            auto& prevSym = scope.asSymbol();
            if (prevSym.kind == SymbolKind::Modport) {
                symbol = prevSym.getParentScope()->find(name.text());
                if (symbol) {
                    // Variables, nets, subroutines can only be accessed via the modport.
                    // Other symbols aren't permitted in a modport, so they are allowed
                    // to be accessed through it as if we had accessed the interface
                    // instance itself.
                    if (SemanticFacts::isAllowedInModport(symbol->kind)) {
                        // This is an error, the modport disallows access.
                        auto def = prevSym.getDeclaringDefinition();
                        ASSERT(def);

                        auto& diag =
                            result.addDiag(context.scope, diag::InvalidModportAccess, name.range());
                        diag << name.text();
                        diag << def->name;
                        diag << prevSym.name;
                        return false;
                    }
                    else {
                        // This is fine, we found what we needed.
                        continue;
                    }
                }
            }

            // Give a slightly nicer error if this is a compilation unit lookup.
            DiagCode code = diag::CouldNotResolveHierarchicalPath;
            if (prevSym.kind == SymbolKind::CompilationUnit)
                code = diag::UnknownUnitMember;

            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << name.text();
            diag << name.range();
            return true;
        }
    }

    if (!checkClassParams(name))
        return false;

    // If we found an automatic variable check that we didn't try to reference it hierarchically.
    if (result.isHierarchical && symbol && VariableSymbol::isKind(symbol->kind) &&
        symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
        result.addDiag(context.scope, diag::AutoVariableHierarchical, name.range());
        return false;
    }

    result.found = symbol;
    if (name.selectors)
        result.selectors.appendRange(*name.selectors);

    return true;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupUpward(Compilation& compilation, span<const NamePlusLoc> nameParts,
                  const NameComponents& name, const BindContext& context, LookupResult& result,
                  bitmask<LookupFlags> flags) {

    // Upward lookups can match either a scope name, or a module definition name (on any of the
    // instances). Imports are not considered.
    const Symbol* firstMatch = nullptr;
    const Scope* scope = &context.scope;
    while (true) {
        const Scope* nextInstance = nullptr;

        while (scope) {
            auto symbol = scope->find(name.text());
            if (!symbol || symbol->isValue() || symbol->isType() ||
                (!symbol->isScope() && symbol->kind != SymbolKind::Instance)) {
                // We didn't find an instance name, so now look at the definition types of each
                // instance.
                symbol = nullptr;
                for (auto& instance : scope->membersOfType<InstanceSymbol>()) {
                    if (instance.getDefinition().name == name.text()) {
                        if (!symbol)
                            symbol = &instance;
                        else {
                            // TODO: error
                        }
                    }
                }
            }

            if (symbol) {
                // Keep track of the first match we find; if it turns out we can't
                // resolve all of the name parts we'll move on and try elsewhere,
                // but at the end if we couldn't find a full match we'll use this to
                // provide a better error.
                if (!firstMatch)
                    firstMatch = symbol;

                result.clear();
                result.found = symbol;

                if (!lookupDownward(nameParts, name, context, result, flags))
                    return false;

                if (result.found)
                    return true;
            }

            // Figure out which scope to look at next. If we're already at the root scope, we're
            // done and should return. Otherwise, we want to keep going up until we hit the
            // compilation unit, at which point we'll jump back to the instantiation scope of
            // the last instance we hit.
            symbol = &scope->asSymbol();
            switch (symbol->kind) {
                case SymbolKind::Root:
                    result.clear();
                    if (firstMatch) {
                        // If we did find a match at some point, repeat that
                        // lookup to provide a real error message.
                        result.found = firstMatch;
                        lookupDownward(nameParts, name, context, result, flags);
                        return false;
                    }
                    return true;
                case SymbolKind::CompilationUnit:
                    scope = nullptr;
                    break;
                case SymbolKind::InstanceBody: {
                    // TODO: This will only look at one of our instance parents, but there
                    // may be many, instantiated in such a way that some of them are invalid.
                    // We need to check that somewhere at some point.
                    //
                    // TODO: if this is a nested module it may do the wrong thing...
                    auto parents = compilation.getParentInstances(symbol->as<InstanceBodySymbol>());
                    if (!parents.empty())
                        nextInstance = parents[0]->getParentScope();

                    scope = symbol->getParentScope();
                    break;
                }
                default:
                    scope = symbol->getParentScope();
                    break;
            }
        }

        if (nextInstance)
            scope = nextInstance;
        else
            scope = &compilation.getRoot();
    }
}

bool checkVisibility(const Symbol& symbol, const Scope& scope, optional<SourceRange> sourceRange,
                     LookupResult& result) {
    // All public members and all non-class symbols are visible by default.
    Visibility visibility = Lookup::getVisibility(symbol);
    if (visibility == Visibility::Public)
        return true;

    // All non-public members can only be accessed from scopes that are within a class.
    const Symbol* lookupParent = Lookup::getContainingClass(scope);
    const Symbol& targetParent = symbol.getParentScope()->asSymbol();

    if (lookupParent && targetParent.kind == SymbolKind::ClassType) {
        if (visibility == Visibility::Local) {
            // Local members can only be accessed from the declaring class,
            // or from any nested classes within that class.
            do {
                if (lookupParent == &targetParent)
                    return true;

                lookupParent = &lookupParent->getParentScope()->asSymbol();
            } while (lookupParent->kind == SymbolKind::ClassType);
        }
        else {
            // Protected members can be accessed from derived classes as well,
            // in addition to nested classes within those derived classes.
            auto& targetType = targetParent.as<Type>();
            do {
                auto& sourceType = lookupParent->as<Type>();
                if (targetType.isAssignmentCompatible(sourceType))
                    return true;

                lookupParent = &lookupParent->getParentScope()->asSymbol();
            } while (lookupParent->kind == SymbolKind::ClassType);
        }
    }

    if (sourceRange) {
        if (symbol.name == "new") {
            auto& diag = result.addDiag(scope, diag::InvalidConstructorAccess, *sourceRange);
            diag << targetParent.name;
            if (visibility == Visibility::Local)
                diag << LexerFacts::getTokenKindText(TokenKind::LocalKeyword);
            else
                diag << LexerFacts::getTokenKindText(TokenKind::ProtectedKeyword);

            diag.addNote(diag::NoteDeclarationHere, symbol.location);
        }
        else {
            auto code = visibility == Visibility::Local ? diag::LocalMemberAccess
                                                        : diag::ProtectedMemberAccess;
            auto& diag = result.addDiag(scope, code, *sourceRange);
            diag << symbol.name << targetParent.name;
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
        }
    }

    return false;
}

bool resolveColonNames(SmallVectorSized<NamePlusLoc, 8>& nameParts, int colonParts,
                       NameComponents& name, bitmask<LookupFlags> flags, LookupResult& result,
                       const BindContext& context) {
    const Symbol* symbol = std::exchange(result.found, nullptr);
    ASSERT(symbol);

    // The initial symbol found cannot be resolved via a forward typedef (i.e. "incomplete")
    // unless this is within a typedef declaration.
    if (result.fromForwardTypedef && (flags & LookupFlags::TypedefTarget) == 0)
        result.addDiag(context.scope, diag::ScopeIncompleteTypedef, name.range());

    auto validateSymbol = [&] {
        // Handle generic classes and parameter assignments. If this is a generic class,
        // we must have param assignments here (even if the generic class has a default
        // specialization, the spec says you can't use that with colon-scoped lookup).
        if (symbol->kind == SymbolKind::GenericClassDef) {
            if (name.paramAssignments) {
                auto& type = symbol->as<GenericClassDefSymbol>().getSpecialization(
                    context, *name.paramAssignments);
                if (type.isError())
                    return false;

                symbol = &type;
                name.paramAssignments = nullptr;
            }
            else {
                // The unadorned generic class name here is an error if we're outside the context
                // of the class itself. If we're within the class, it refers to the "current"
                // specialization, not the default specialization.
                auto parent = Lookup::getContainingClass(context.scope);
                if (!parent || parent->genericClass != symbol) {
                    result.addDiag(context.scope, diag::GenericClassScopeResolution, name.range());
                    return false;
                }
                symbol = parent;
            }
        }
        else if (name.paramAssignments) {
            auto& diag = result.addDiag(context.scope, diag::NotAGenericClass, name.range());
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return false;
        }

        // If this is a type alias, check its visibility.
        checkVisibility(*symbol, context.scope, name.range(), result);

        return true;
    };

    bool isClass = false;
    while (colonParts--) {
        if (name.selectors) {
            result.addDiag(context.scope, diag::InvalidScopeIndexExpression,
                           name.selectors->sourceRange());
            return false;
        }

        auto& part = nameParts.back();
        symbol = unwrapTypeParam(symbol);
        if (!symbol)
            return false;

        isClass = isClassType(*symbol);
        if (symbol->kind != SymbolKind::Package && !isClass) {
            auto& diag = result.addDiag(context.scope, diag::NotAClass, part.dotLocation);
            diag << name.range();
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return false;
        }

        if (!validateSymbol())
            return false;

        name = *part.name;
        if (name.text().empty())
            return false;

        if (symbol->isType())
            symbol = &symbol->as<Type>().getCanonicalType();

        const Symbol* savedSymbol = symbol;
        symbol = symbol->as<Scope>().find(name.text());
        if (!symbol) {
            DiagCode code = diag::UnknownClassMember;
            if (savedSymbol->kind == SymbolKind::Package)
                code = diag::UnknownPackageMember;

            auto& diag = result.addDiag(context.scope, code, part.dotLocation);
            diag << name.text();
            diag << name.range();
            diag << savedSymbol->name;
            return false;
        }

        nameParts.pop();
    }

    if (!validateSymbol())
        return false;

    result.found = symbol;
    return true;
}

const Symbol* getCompilationUnit(const Symbol& symbol) {
    const Symbol* current = &symbol;
    while (true) {
        if (current->kind == SymbolKind::CompilationUnit)
            return current;

        auto scope = current->getParentScope();
        ASSERT(scope);

        current = &scope->asSymbol();
    }
}

void unwrapResult(const Scope& scope, optional<SourceRange> range, LookupResult& result) {
    if (!result.found)
        return;

    checkVisibility(*result.found, scope, range, result);

    // Unwrap type parameters into their target type alias.
    if (result.found->kind == SymbolKind::TypeParameter) {
        result.found = &result.found->as<TypeParameterSymbol>().getTypeAlias();
        result.fromTypeParam = true;
    }

    // If the found symbol is a generic class, unwrap into
    // the default specialization (if possible).
    if (result.found->kind == SymbolKind::GenericClassDef) {
        auto& genericClass = result.found->as<GenericClassDefSymbol>();
        result.found = genericClass.getDefaultSpecialization();

        if (!result.found && range)
            result.addDiag(scope, diag::NoDefaultSpecialization, *range) << genericClass.name;
    }
}

const Symbol* findThisHandle(const Scope& scope, SourceRange range, LookupResult& result) {
    // Find the parent method, if we can.
    const Symbol* parent = &scope.asSymbol();
    while (parent->kind == SymbolKind::StatementBlock) {
        auto parentScope = parent->getParentScope();
        ASSERT(parentScope);
        parent = &parentScope->asSymbol();
    }

    if (parent->kind == SymbolKind::Subroutine) {
        auto& sub = parent->as<SubroutineSymbol>();
        if (sub.thisVar)
            return sub.thisVar;
    }

    result.addDiag(scope, diag::InvalidThisHandle, range);
    return nullptr;
}

const Symbol* findSuperHandle(const Scope& scope, SourceRange range, LookupResult& result) {
    auto parent = Lookup::getContainingClass(scope);
    if (!parent) {
        result.addDiag(scope, diag::SuperOutsideClass, range);
        return nullptr;
    }

    auto base = parent->getBaseClass();
    if (!base) {
        result.addDiag(scope, diag::SuperNoBase, range) << parent->name;
        return nullptr;
    }

    return base;
}

} // namespace

void Lookup::name(const Scope& scope, const NameSyntax& syntax, LookupLocation location,
                  bitmask<LookupFlags> flags, LookupResult& result) {
    NameComponents name;
    switch (syntax.kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            name = syntax;
            break;
        case SyntaxKind::ScopedName:
            // Handle qualified names separately.
            qualified(scope, syntax.as<ScopedNameSyntax>(), location, flags, result);
            unwrapResult(scope, syntax.sourceRange(), result);
            return;
        case SyntaxKind::ThisHandle:
            result.found = findThisHandle(scope, syntax.sourceRange(), result);
            return;
        case SyntaxKind::SystemName: {
            // If this is a system name, look up directly in the compilation.
            Token nameToken = syntax.as<SystemNameSyntax>().systemIdentifier;
            result.found = nullptr;
            result.systemSubroutine =
                scope.getCompilation().getSystemSubroutine(nameToken.valueText());

            if (!result.systemSubroutine) {
                result.addDiag(scope, diag::UnknownSystemName, nameToken.range())
                    << nameToken.valueText();
            }
            return;
        }
        default:
            THROW_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    if (name.text().empty())
        return;

    // Perform the lookup.
    unqualifiedImpl(scope, name.text(), location, name.range(), flags, {}, result);
    if (!result.found && !result.hasError())
        reportUndeclared(scope, name.text(), name.range(), flags, false, result);

    if (result.found && name.paramAssignments) {
        if (result.found->kind != SymbolKind::GenericClassDef) {
            auto& diag = result.addDiag(scope, diag::NotAGenericClass, syntax.sourceRange());
            diag << result.found->name;
            diag.addNote(diag::NoteDeclarationHere, result.found->location);

            result.found = nullptr;
        }
        else {
            auto& classDef = result.found->as<GenericClassDefSymbol>();
            result.found =
                &classDef.getSpecialization(BindContext(scope, location), *name.paramAssignments);
        }
    }

    unwrapResult(scope, syntax.sourceRange(), result);

    if (name.selectors) {
        // If this is a scope, the selectors should be an index into it.
        if (result.found && result.found->isScope() && !result.found->isType()) {
            result.found =
                selectChild(*result.found, *name.selectors, BindContext(scope, location), result);
        }
        else {
            result.selectors.appendRange(*name.selectors);
        }
    }
}

const Symbol* Lookup::unqualified(const Scope& scope, string_view name,
                                  bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, LookupLocation::max, std::nullopt, flags, {}, result);
    ASSERT(result.selectors.empty());
    unwrapResult(scope, std::nullopt, result);

    return result.found;
}

const Symbol* Lookup::unqualifiedAt(const Scope& scope, string_view name, LookupLocation location,
                                    SourceRange sourceRange, bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, location, sourceRange, flags, {}, result);
    ASSERT(result.selectors.empty());
    unwrapResult(scope, sourceRange, result);

    if (!result.found && !result.hasError())
        reportUndeclared(scope, name, sourceRange, flags, false, result);

    if (result.hasError())
        scope.getCompilation().addDiagnostics(result.getDiagnostics());

    return result.found;
}

const Symbol* Lookup::selectChild(const Symbol& initialSymbol,
                                  span<const ElementSelectSyntax* const> selectors,
                                  const BindContext& context, LookupResult& result) {
    const Symbol* symbol = &initialSymbol;
    for (const ElementSelectSyntax* syntax : selectors) {
        if (!syntax->selector || syntax->selector->kind != SyntaxKind::BitSelect) {
            result.addDiag(context.scope, diag::InvalidScopeIndexExpression, syntax->sourceRange());
            return nullptr;
        }

        auto index = context.evalInteger(*syntax->selector->as<BitSelectSyntax>().expr);
        if (!index)
            return nullptr;

        switch (symbol->kind) {
            case SymbolKind::InstanceArray: {
                auto& array = symbol->as<InstanceArraySymbol>();
                if (array.elements.empty())
                    return nullptr;

                if (!array.range.containsPoint(*index)) {
                    auto& diag = result.addDiag(context.scope, diag::ScopeIndexOutOfRange,
                                                syntax->sourceRange());
                    diag << *index;
                    diag.addNote(diag::NoteDeclarationHere, symbol->location);
                    return nullptr;
                }

                symbol = array.elements[size_t(array.range.translateIndex(*index))];
                break;
            }
            case SymbolKind::GenerateBlockArray: {
                bool found = false;
                auto& array = symbol->as<GenerateBlockArraySymbol>();
                if (!array.valid)
                    return nullptr;

                for (auto& entry : array.entries) {
                    if (*entry.index == *index) {
                        found = true;
                        symbol = entry.block;
                        break;
                    }
                }

                if (!found) {
                    auto& diag = result.addDiag(context.scope, diag::ScopeIndexOutOfRange,
                                                syntax->sourceRange());
                    diag << *index;
                    diag.addNote(diag::NoteDeclarationHere, symbol->location);
                    return nullptr;
                }
                break;
            }
            default: {
                // I think it's safe to assume that the symbol name here will not be empty
                // because if it was, it'd be an instance array or generate array.
                auto& diag =
                    result.addDiag(context.scope, diag::ScopeNotIndexable, syntax->sourceRange());
                diag << symbol->name;
                diag.addNote(diag::NoteDeclarationHere, symbol->location);
                return nullptr;
            }
        }
    }

    return symbol;
}

const ClassType* Lookup::findClass(const NameSyntax& className, const BindContext& context,
                                   optional<DiagCode> requireInterfaceClass) {
    LookupResult result;
    Lookup::name(context.scope, className, context.lookupLocation, LookupFlags::Type, result);

    result.reportErrors(context);
    if (!result.found)
        return nullptr;

    if (requireInterfaceClass) {
        if (result.fromTypeParam) {
            context.addDiag(diag::IfaceExtendTypeParam, className.sourceRange());
            return nullptr;
        }

        if (result.fromForwardTypedef) {
            context.addDiag(diag::IfaceExtendIncomplete, className.sourceRange());
            return nullptr;
        }
    }

    if (!result.found->isType() || !result.found->as<Type>().isClass()) {
        if (!result.found->isType() || !result.found->as<Type>().isError())
            context.addDiag(diag::NotAClass, className.sourceRange()) << result.found->name;
        return nullptr;
    }

    auto& classType = result.found->as<Type>().getCanonicalType().as<ClassType>();

    if (requireInterfaceClass && !classType.isInterface) {
        context.addDiag(*requireInterfaceClass, className.sourceRange()) << classType.name;
        return nullptr;
    }

    return &classType;
}

const ClassType* Lookup::getContainingClass(const Scope& scope) {
    const Symbol* parent = &scope.asSymbol();
    while (parent->kind == SymbolKind::StatementBlock || parent->kind == SymbolKind::Subroutine) {
        auto parentScope = parent->getParentScope();
        ASSERT(parentScope);
        parent = &parentScope->asSymbol();
    }

    if (parent->kind == SymbolKind::ClassType)
        return &parent->as<ClassType>();

    return nullptr;
}

Visibility Lookup::getVisibility(const Symbol& symbol) {
    switch (symbol.kind) {
        case SymbolKind::MethodPrototype:
            return symbol.as<MethodPrototypeSymbol>().visibility;
        case SymbolKind::ClassProperty:
            return symbol.as<ClassPropertySymbol>().visibility;
        case SymbolKind::Subroutine:
            return symbol.as<SubroutineSymbol>().visibility;
        case SymbolKind::TypeAlias:
            return symbol.as<TypeAliasType>().visibility;
        default:
            return Visibility::Public;
    }
}

bool Lookup::isVisibleFrom(const Symbol& symbol, const Scope& scope) {
    LookupResult result;
    return checkVisibility(symbol, scope, std::nullopt, result);
}

bool Lookup::ensureVisible(const Symbol& symbol, const BindContext& context,
                           optional<SourceRange> sourceRange) {
    LookupResult result;
    if (checkVisibility(symbol, context.scope, sourceRange, result))
        return true;

    result.reportErrors(context);
    return false;
}

bool Lookup::findIterator(const Scope& scope, const IteratorSymbol& symbol,
                          const NameSyntax& syntax, LookupResult& result) {
    int colonParts = 0;
    SmallVectorSized<NamePlusLoc, 8> nameParts;
    const NameSyntax* first = &syntax;
    if (syntax.kind == SyntaxKind::ScopedName) {
        first = splitScopedName(syntax.as<ScopedNameSyntax>(), nameParts, colonParts);
        if (colonParts)
            return false;
    }

    NameComponents name;
    switch (first->kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            name = *first;
            break;
        default:
            return false;
    }

    const IteratorSymbol* curr = &symbol;
    do {
        if (curr->name == name.text()) {
            result.found = curr;
            break;
        }
        curr = curr->nextIterator;
    } while (curr);

    if (!result.found)
        return false;

    BindContext context(scope, LookupLocation::max);
    if (!lookupDownward(nameParts, name, context, result, LookupFlags::None))
        return false;

    return true;
}

void Lookup::unqualifiedImpl(const Scope& scope, string_view name, LookupLocation location,
                             optional<SourceRange> sourceRange, bitmask<LookupFlags> flags,
                             SymbolIndex outOfBlockIndex, LookupResult& result) {
    // Try a simple name lookup to see if we find anything.
    auto& nameMap = scope.getNameMap();
    const Symbol* symbol = nullptr;
    if (auto it = nameMap.find(name); it != nameMap.end()) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the
        // scope, so the location doesn't matter for them.
        symbol = it->second;
        bool locationGood = true;
        if (!flags.has(LookupFlags::AllowDeclaredAfter)) {
            locationGood = LookupLocation::before(*symbol) < location;
            if (!locationGood) {
                // A type alias can have forward definitions, so check those locations as well.
                // The forward decls form a linked list that are always ordered by location,
                // so we only need to check the first one.
                const ForwardingTypedefSymbol* forward = nullptr;
                switch (symbol->kind) {
                    case SymbolKind::TypeAlias:
                        forward = symbol->as<TypeAliasType>().getFirstForwardDecl();
                        break;
                    case SymbolKind::ClassType:
                        forward = symbol->as<ClassType>().getFirstForwardDecl();
                        break;
                    case SymbolKind::GenericClassDef:
                        forward = symbol->as<GenericClassDefSymbol>().getFirstForwardDecl();
                        break;
                    case SymbolKind::Subroutine:
                        // Subroutines can be referenced before they are declared if they
                        // are tasks or return void (tasks are always set to have a void
                        // return type internally so we only need one check here).
                        locationGood = symbol->as<SubroutineSymbol>().getReturnType().isVoid();
                        break;
                    case SymbolKind::MethodPrototype:
                        // Same as above.
                        locationGood = symbol->as<MethodPrototypeSymbol>().getReturnType().isVoid();
                        break;
                    default:
                        break;
                }

                if (forward) {
                    locationGood = LookupLocation::before(*forward) < location;
                    result.fromForwardTypedef = true;
                }
            }
        }

        if (locationGood) {
            // Unwrap the symbol if it's hidden behind an import or hoisted enum member.
            while (symbol->kind == SymbolKind::TransparentMember)
                symbol = &symbol->as<TransparentMemberSymbol>().wrapped;

            switch (symbol->kind) {
                case SymbolKind::ExplicitImport:
                    result.found = symbol->as<ExplicitImportSymbol>().importedSymbol();
                    result.wasImported = true;
                    break;
                case SymbolKind::ForwardingTypedef:
                    // If we find a forwarding typedef, the actual typedef was never defined.
                    // Just ignore it, we'll issue a better error later.
                    break;
                case SymbolKind::MethodPrototype:
                    // Looking up a prototype should always forward on to the actual method.
                    result.found = symbol->as<MethodPrototypeSymbol>().getSubroutine();
                    break;
                default:
                    result.found = symbol;
                    break;
            }

            // We have a fully resolved and valid symbol. Before we return back to the caller,
            // make sure that the symbol we're returning isn't in the process of having its type
            // evaluated. This can only happen with a mutually recursive definition of something
            // like a parameter and a function, so detect and report the error here to avoid a
            // stack overflow.
            if (result.found) {
                const DeclaredType* declaredType = result.found->getDeclaredType();
                if (declaredType && declaredType->isEvaluating()) {
                    if (sourceRange) {
                        auto& diag = result.addDiag(scope, diag::RecursiveDefinition, *sourceRange);
                        diag << name;
                        diag.addNote(diag::NoteDeclarationHere, result.found->location);
                    }
                    result.found = nullptr;
                }
            }

            return;
        }
    }

    // Look through any wildcard imports prior to the lookup point and see if their packages
    // contain the name we're looking for.
    struct Import {
        const Symbol* imported;
        const WildcardImportSymbol* import;
    };
    SmallVectorSized<Import, 8> imports;

    for (auto import : scope.getWildcardImports()) {
        if (location < LookupLocation::after(*import))
            break;

        auto package = import->getPackage();
        if (!package) {
            result.sawBadImport = true;
            continue;
        }

        const Symbol* imported = package->find(name);
        if (imported)
            imports.emplace(Import{ imported, import });
    }

    if (!imports.empty()) {
        if (imports.size() > 1) {
            if (sourceRange) {
                auto& diag = result.addDiag(scope, diag::AmbiguousWildcardImport, *sourceRange);
                diag << name;
                for (const auto& pair : imports) {
                    diag.addNote(diag::NoteImportedFrom, pair.import->location);
                    diag.addNote(diag::NoteDeclarationHere, pair.imported->location);
                }
            }
            return;
        }

        if (symbol && sourceRange) {
            auto& diag = result.addDiag(scope, diag::ImportNameCollision, *sourceRange) << name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            diag.addNote(diag::NoteImportedFrom, imports[0].import->location);
            diag.addNote(diag::NoteDeclarationHere, imports[0].imported->location);
        }

        result.wasImported = true;
        result.found = imports[0].imported;
        return;
    }

    // Continue up the scope chain via our parent.
    location = LookupLocation::after(scope.asSymbol());
    if (!location.getScope())
        return;

    // If this scope was an out-of-block subroutine, tell the next recursive call about it.
    // Otherwise, if our previous call was for such a situation and we didn't find the symbol
    // in this class scope, we need to use the subroutine's out-of-block lookup location
    // instead in order to properly handle cases like:
    //   class C;
    //     extern function int foo;
    //   endclass
    //   localparam int k = ...;
    //   function int C::foo;
    //     return k;
    //   endfunction
    if (scope.asSymbol().kind == SymbolKind::Subroutine)
        outOfBlockIndex = scope.asSymbol().as<SubroutineSymbol>().outOfBlockIndex;
    else if (uint32_t(outOfBlockIndex) != 0) {
        location = LookupLocation(location.getScope(), uint32_t(outOfBlockIndex));
        outOfBlockIndex = SymbolIndex(0);
    }

    return unqualifiedImpl(*location.getScope(), name, location, sourceRange, flags,
                           outOfBlockIndex, result);
}

static bool isUninstantiated(const Scope& scope) {
    auto currScope = &scope;
    while (currScope && currScope->asSymbol().kind != SymbolKind::InstanceBody)
        currScope = currScope->asSymbol().getParentScope();

    if (currScope)
        return currScope->asSymbol().as<InstanceBodySymbol>().isUninstantiated;

    return false;
}

void Lookup::qualified(const Scope& scope, const ScopedNameSyntax& syntax, LookupLocation location,
                       bitmask<LookupFlags> flags, LookupResult& result) {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    int colonParts = 0;
    SmallVectorSized<NamePlusLoc, 8> nameParts;
    auto leftMost = splitScopedName(syntax, nameParts, colonParts);

    NameComponents first = *leftMost;
    auto name = first.text();
    if (name.empty())
        return;

    auto& compilation = scope.getCompilation();
    if (compilation.isFinalizing())
        flags |= LookupFlags::Constant;

    BindContext context(scope, location);
    bool inConstantEval = (flags & LookupFlags::Constant) != 0;

    switch (leftMost->kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            // Start by trying to find the first name segment using normal unqualified lookup
            unqualifiedImpl(scope, name, location, first.range(), flags, {}, result);
            break;
        case SyntaxKind::UnitScope:
            // Ignore hierarchical lookups that occur inside uninstantiated modules.
            if (isUninstantiated(scope))
                return;

            result.found = getCompilationUnit(scope.asSymbol());
            lookupDownward(nameParts, first, context, result, flags);
            return;
        case SyntaxKind::RootScope:
            // Be careful to avoid calling getRoot() if we're in a constant context (there's a
            // chance we could already be in the middle of calling getRoot in that case).
            if (inConstantEval) {
                result.isHierarchical = true;
                result.addDiag(scope, diag::HierarchicalNotAllowedInConstant, first.range());
                return;
            }

            // Ignore hierarchical lookups that occur inside uninstantiated modules.
            if (isUninstantiated(scope))
                return;

            result.found = &compilation.getRoot();
            lookupDownward(nameParts, first, context, result, flags);
            return;
        case SyntaxKind::ThisHandle:
            result.found = findThisHandle(scope, first.range(), result);
            if (result.found && nameParts.back().name->kind == SyntaxKind::SuperHandle) {
                // Handle "this.super.whatever" the same as if the user had just
                // written "super.whatever".
                first = *nameParts.back().name;
                nameParts.pop();
                result.found = findSuperHandle(scope, first.range(), result);
                colonParts = 1;
            }
            break;
        case SyntaxKind::SuperHandle:
            result.found = findSuperHandle(scope, first.range(), result);
            colonParts = 1; // pretend we used colon access to resolve class scoped name
            break;
        case SyntaxKind::LocalScope:
            result.addDiag(scope, diag::NotYetSupported, syntax.sourceRange());
            return;
        default:
            THROW_UNREACHABLE;
    }

    if (result.hasError())
        return;

    // [23.7.1] If we are starting with a colon separator, always do a downwards name
    // resolution.
    if (colonParts) {
        // Unwrap the symbol if it's a type parameter, and bail early if it's an error type.
        if (result.found) {
            result.found = unwrapTypeParam(result.found);
            if (!result.found)
                return;
        }

        // If the prefix name resolved normally to a class object, use that. Otherwise we need
        // to look for a package with the corresponding name.
        if (!result.found || !isClassType(*result.found)) {
            result.found = compilation.getPackage(name);
            if (!result.found) {
                if (!isUninstantiated(scope))
                    result.addDiag(scope, diag::UnknownClassOrPackage, first.range()) << name;
                return;
            }
        }

        // Drain all colon-qualified lookups here, which should always resolve to a nested type.
        if (!resolveColonNames(nameParts, colonParts, first, flags, result, context))
            return;

        // We can't do upwards name resolution if colon access is involved, so always return
        // after one downward lookup.
        lookupDownward(nameParts, first, context, result, flags);
        return;
    }

    // [23.7] lists the possible cases for dotted names:
    // 1. The name resolves to a value symbol. The dotted name is a member select.
    // 2. The name resolves to a local scope. The dotted name is a hierarchical reference.
    // 3. The name resolves to an imported scope. The dotted name is a hierarchical reference,
    //    but with an added restriction that only a direct downward lookup from the package is
    //    allowed.
    // 4. The name is not found; it's considered a hierarchical reference and participates in
    //    upwards name resolution.

    LookupResult originalResult;
    if (result.found) {
        // Perform the downward lookup.
        if (!lookupDownward(nameParts, first, context, result, flags))
            return;

        // If we found a symbol, we're done with lookup. In case (1) above we'll always have a
        // found symbol here. Otherwise, if we're in case (2) we need to do further upwards name
        // lookup. If we're in case (3) we've already issued an error and just need to give up.
        if (result.found || result.wasImported)
            return;

        if (inConstantEval) {
            // An appropriate error was already issued in lookupDownward()
            return;
        }

        originalResult.copyFrom(result);
    }
    else if (inConstantEval) {
        // We can't perform upward lookups during constant evaluation so just report an unknown
        // identifier.
        reportUndeclared(scope, name, first.range(), flags, true, result);
        return;
    }

    // If we reach this point we're in case (2) or (4) above. Go up through the instantiation
    // hierarchy and see if we can find a match there.
    if (!lookupUpward(compilation, nameParts, first, context, result, flags))
        return;

    if (result.found)
        return;

    // We couldn't find anything. originalResult has any diagnostics issued by the first
    // downward lookup (if any), so it's fine to just return it as is. If we never found any
    // symbol originally, issue an appropriate error for that.
    result.copyFrom(originalResult);
    if (!result.found && !result.hasError() && !isUninstantiated(scope))
        reportUndeclared(scope, name, first.range(), flags, true, result);
}

void Lookup::reportUndeclared(const Scope& initialScope, string_view name, SourceRange range,
                              bitmask<LookupFlags> flags, bool isHierarchical,
                              LookupResult& result) {
    // If the user doesn't want an error, don't give him one.
    if ((flags & LookupFlags::NoUndeclaredError) != 0)
        return;

    // If we observed a wildcard import we couldn't resolve, we shouldn't report an
    // error for undeclared identifier because maybe it's supposed to come from that package.
    // In particular it's important that we do this because when we first look at a
    // definition because it's possible we haven't seen the file containing the package yet.
    if (result.sawBadImport)
        return;

    // The symbol wasn't found, so this is an error. The only question is how helpful we can
    // make that error. Let's try to find the closest named symbol in all reachable scopes,
    // including package imports, to provide a "did you mean" diagnostic. If along the way
    // we happen to actually find the symbol but it's declared later in the source text,
    // we will use that to issue a "used before declared" diagnostic.
    auto& comp = initialScope.getCompilation();
    const Symbol* actualSym = nullptr;
    const Symbol* closestSym = nullptr;
    int bestDistance = INT_MAX;
    bool usedBeforeDeclared = false;
    auto scope = &initialScope;
    do {
        // This lambda returns true if the given symbol is a viable candidate
        // for the kind of lookup that was being performed.
        auto isViable = [flags, &initialScope](const Symbol& sym) {
            const Symbol* s = &sym;
            if (s->kind == SymbolKind::TransparentMember)
                s = &s->as<TransparentMemberSymbol>().wrapped;

            if (flags & LookupFlags::Type) {
                if (!s->isType() && s->kind != SymbolKind::TypeParameter &&
                    s->kind != SymbolKind::GenericClassDef) {
                    return false;
                }
            }
            else {
                if (!s->isValue() && s->kind != SymbolKind::Subroutine &&
                    s->kind != SymbolKind::InstanceArray &&
                    (s->kind != SymbolKind::Instance || !s->as<InstanceSymbol>().isInterface())) {
                    return false;
                }
            }

            // Ignore special members.
            if (s->kind == SymbolKind::Subroutine &&
                (s->as<SubroutineSymbol>().flags & MethodFlags::Constructor) != 0) {
                return false;
            }

            if (VariableSymbol::isKind(s->kind) && s->as<VariableSymbol>().isCompilerGenerated)
                return false;

            if (!isVisibleFrom(*s, initialScope))
                return false;

            return true;
        };

        if ((flags & LookupFlags::AllowDeclaredAfter) == 0) {
            actualSym = scope->find(name);
            if (actualSym) {
                usedBeforeDeclared = isViable(*actualSym);
                break;
            }
        }

        // Only check for typos if that functionality is enabled -- it can be
        // disabled by config or if we've tried too many times to correct typos.
        if (comp.doTypoCorrection()) {
            auto checkMembers = [&](const Scope& toCheck) {
                for (auto& member : toCheck.members()) {
                    if (member.name.empty() || !isViable(member))
                        continue;

                    int dist =
                        editDistance(member.name, name, /* allowReplacements */ true, bestDistance);
                    if (dist < bestDistance) {
                        closestSym = &member;
                        bestDistance = dist;
                    }
                }
            };

            // Check the current scope.
            checkMembers(*scope);

            // Also search in package imports.
            for (auto import : scope->getWildcardImports()) {
                auto package = import->getPackage();
                if (package)
                    checkMembers(*package);
            }
        }

        scope = scope->asSymbol().getParentScope();
    } while (scope);

    // If we found the actual named symbol and it's viable for our kind of lookup,
    // report a diagnostic about it being used before declared.
    if (usedBeforeDeclared) {
        auto& diag = result.addDiag(initialScope, diag::UsedBeforeDeclared, range);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, actualSym->location);
        return;
    }

    // Otherwise, if we found the symbol but it wasn't viable becaues we're in a
    // constant context, tell the user not to use hierarchical names here.
    if ((flags & LookupFlags::Constant) && actualSym &&
        (actualSym->isScope() || actualSym->kind == SymbolKind::Instance)) {
        result.addDiag(initialScope, diag::HierarchicalNotAllowedInConstant, range);
        return;
    }

    // Otherwise, check if this names a definition, in which case we can give a nicer error.
    auto def = initialScope.getCompilation().getDefinition(name, initialScope);
    if (def) {
        string_view kindStr;
        switch (def->definitionKind) {
            case DefinitionKind::Module:
                kindStr = "a module";
                break;
            case DefinitionKind::Interface:
                kindStr = "an interface";
                break;
            case DefinitionKind::Program:
                kindStr = "a program";
                break;
        }

        DiagCode code =
            (flags & LookupFlags::Type) ? diag::DefinitionUsedAsType : diag::DefinitionUsedAsValue;
        result.addDiag(initialScope, code, range) << name << kindStr;
        return;
    }

    // Count the number of times we've performed typo correction.
    comp.didTypoCorrection();

    // See if we found a viable symbol with a name that's somewhat close to the one we wanted.
    // If we did, assume that the user made a typo and report it.
    if (closestSym && bestDistance > 0 && name.length() / size_t(bestDistance) >= 3) {
        auto& diag = result.addDiag(initialScope, diag::TypoIdentifier, range);
        diag << name << closestSym->name;
        diag.addNote(diag::NoteDeclarationHere, closestSym->location);
        return;
    }

    // We couldn't make any senes of this, just report a simple error about a missing identifier.
    auto& diag = result.addDiag(initialScope, diag::UndeclaredIdentifier, range) << name;
    if (isHierarchical && (flags & LookupFlags::Constant))
        diag.addNote(diag::NoteHierarchicalNameInCE, range.start()) << name;
}

} // namespace slang

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
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/BlockSymbols.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/PortSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
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
    selectors.clear();
    diagnostics.clear();
}

void LookupResult::copyFrom(const LookupResult& other) {
    found = other.found;
    systemSubroutine = other.systemSubroutine;
    wasImported = other.wasImported;
    isHierarchical = other.isHierarchical;
    sawBadImport = other.sawBadImport;

    selectors.clear();
    selectors.appendRange(other.selectors);

    diagnostics.clear();
    diagnostics.appendRange(other.diagnostics);
}

namespace {

struct NamePlusLoc {
    const NameSyntax* name;
    SourceLocation dotLocation;
};

using NameComponent = std::tuple<Token, const SyntaxList<ElementSelectSyntax>*>;

NameComponent decomposeName(const NameSyntax& name) {
    switch (name.kind) {
        case SyntaxKind::IdentifierName:
            return { name.as<IdentifierNameSyntax>().identifier, nullptr };
        case SyntaxKind::SystemName:
            return { name.as<SystemNameSyntax>().systemIdentifier, nullptr };
        case SyntaxKind::IdentifierSelectName: {
            auto& idSelect = name.as<IdentifierSelectNameSyntax>();
            return { idSelect.identifier, &idSelect.selectors };
        }
        case SyntaxKind::ClassName: {
            // TODO: handle class params
            auto& cn = name.as<ClassNameSyntax>();
            return { cn.identifier, nullptr };
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
        case SyntaxKind::ConstructorName: {
            auto& keywordName = name.as<KeywordNameSyntax>();
            return { keywordName.keyword, nullptr };
        }
        default:
            THROW_UNREACHABLE;
    }
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupDownward(span<const NamePlusLoc> nameParts, Token nameToken,
                    const SyntaxList<ElementSelectSyntax>* selectors, const BindContext& context,
                    LookupResult& result, bitmask<LookupFlags> flags) {
    const Symbol* symbol = std::exchange(result.found, nullptr);
    ASSERT(symbol);

    // Loop through each dotted name component and try to find it in the preceeding scope.
    for (auto it = nameParts.rbegin(); it != nameParts.rend(); it++) {
        // If we found a value, the remaining dots are member access expressions.
        if (symbol->isValue()) {
            if (selectors)
                result.selectors.appendRange(*selectors);

            for (; it != nameParts.rend(); it++) {
                Token memberToken;
                std::tie(memberToken, selectors) = decomposeName(*it->name);

                result.selectors.append(LookupResult::MemberSelector{
                    memberToken.valueText(), it->dotLocation, memberToken.range() });

                if (selectors)
                    result.selectors.appendRange(*selectors);
            }

            // Break out to return the symbol.
            selectors = nullptr;
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

        if (symbol->kind == SymbolKind::InterfacePort) {
            // TODO: modports
            symbol = symbol->as<InterfacePortSymbol>().getConnection();
            if (!symbol)
                return false;
        }

        if ((!symbol->isScope() && symbol->kind != SymbolKind::Instance) || symbol->isType()) {
            auto code = symbol->isType() ? diag::DotOnType : diag::NotAHierarchicalScope;
            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << nameToken.range();
            diag << it->name->sourceRange();

            if (!symbol->isType())
                diag << nameToken.valueText();

            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return true;
        }

        if (result.isHierarchical && (flags & LookupFlags::Constant) != 0) {
            auto& diag = result.addDiag(context.scope, diag::HierarchicalNotAllowedInConstant,
                                        it->dotLocation);
            diag << nameToken.range();
            return false;
        }

        if (selectors) {
            symbol = Lookup::selectChild(*symbol, *selectors, context, result);
            if (!symbol)
                return false;
        }

        if (symbol->kind == SymbolKind::Instance)
            symbol = &symbol->as<InstanceSymbol>().body;

        SymbolKind previousKind = symbol->kind;
        string_view packageName = symbol->kind == SymbolKind::Package ? symbol->name : "";
        const Scope& current = symbol->as<Scope>();

        std::tie(nameToken, selectors) = decomposeName(*it->name);
        if (nameToken.valueText().empty())
            return false;

        symbol = current.find(nameToken.valueText());
        if (!symbol) {
            // Give a slightly nicer error if this is the first component in a package lookup.
            DiagCode code = diag::CouldNotResolveHierarchicalPath;
            if (!packageName.empty())
                code = diag::UnknownPackageMember;
            else if (previousKind == SymbolKind::CompilationUnit)
                code = diag::UnknownUnitMember;

            auto& diag = result.addDiag(context.scope, code, it->dotLocation);
            diag << nameToken.valueText();
            diag << nameToken.range();

            if (!packageName.empty())
                diag << packageName;

            return true;
        }
    }

    // If we found an automatic variable check that we didn't try to reference it hierarchically.
    if (result.isHierarchical && symbol && VariableSymbol::isKind(symbol->kind) &&
        symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
        result.addDiag(context.scope, diag::AutoVariableHierarchical, nameToken.range());
        return false;
    }

    result.found = symbol;
    if (selectors)
        result.selectors.appendRange(*selectors);

    return true;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupUpward(Compilation& compilation, string_view name, span<const NamePlusLoc> nameParts,
                  Token nameToken, const SyntaxList<ElementSelectSyntax>* selectors,
                  const BindContext& context, LookupResult& result, bitmask<LookupFlags> flags) {

    // Upward lookups can match either a scope name, or a module definition name (on any of the
    // instances). Imports are not considered.
    const Symbol* firstMatch = nullptr;
    const Scope* scope = &context.scope;
    while (true) {
        const Scope* nextInstance = nullptr;

        while (scope) {
            auto symbol = scope->find(name);
            if (!symbol || symbol->isValue() || symbol->isType() ||
                (!symbol->isScope() && symbol->kind != SymbolKind::Instance)) {
                // We didn't find an instance name, so now look at the definition types of each
                // instance.
                symbol = nullptr;
                for (auto& instance : scope->membersOfType<InstanceSymbol>()) {
                    if (instance.getDefinition().name == name) {
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

                if (!lookupDownward(nameParts, nameToken, selectors, context, result, flags))
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
                        lookupDownward(nameParts, nameToken, selectors, context, result, flags);
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

void unwrapResult(LookupResult& result) {
    // Unwrap type parameters into their target type alias.
    if (result.found && result.found->kind == SymbolKind::TypeParameter)
        result.found = &result.found->as<TypeParameterSymbol>().getTypeAlias();
}

} // namespace

void Lookup::name(const Scope& scope, const NameSyntax& syntax, LookupLocation location,
                  bitmask<LookupFlags> flags, LookupResult& result) {
    Token nameToken;
    const SyntaxList<ElementSelectSyntax>* selectors = nullptr;
    switch (syntax.kind) {
        case SyntaxKind::IdentifierName:
            nameToken = syntax.as<IdentifierNameSyntax>().identifier;
            break;
        case SyntaxKind::IdentifierSelectName: {
            const auto& selectSyntax = syntax.as<IdentifierSelectNameSyntax>();
            nameToken = selectSyntax.identifier;
            selectors = &selectSyntax.selectors;
            break;
        }
        case SyntaxKind::ScopedName:
            // Handle qualified names completely separately.
            qualified(scope, syntax.as<ScopedNameSyntax>(), location, flags, result);
            unwrapResult(result);
            return;
        case SyntaxKind::ThisHandle:
        case SyntaxKind::ClassName:
            result.addDiag(scope, diag::NotYetSupported, syntax.sourceRange());
            result.found = nullptr;
            return;
        case SyntaxKind::SystemName: {
            // If this is a system name, look up directly in the compilation.
            nameToken = syntax.as<SystemNameSyntax>().systemIdentifier;
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
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    // Perform the lookup.
    unqualifiedImpl(scope, name, location, nameToken.range(), flags, result);
    if (!result.found && !result.hasError())
        reportUndeclared(scope, name, nameToken.range(), flags, false, result);

    unwrapResult(result);

    if (selectors) {
        // If this is a scope, the selectors should be an index into it.
        if (result.found && result.found->isScope() && !result.found->isType()) {
            result.found =
                selectChild(*result.found, *selectors, BindContext(scope, location), result);
        }
        else {
            result.selectors.appendRange(*selectors);
        }
    }
}

const Symbol* Lookup::unqualified(const Scope& scope, string_view name,
                                  bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, LookupLocation::max, SourceRange(), flags, result);
    ASSERT(result.selectors.empty());
    unwrapResult(result);

    return result.found;
}

const Symbol* Lookup::unqualifiedAt(const Scope& scope, string_view name, LookupLocation location,
                                    SourceRange sourceRange, bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, location, sourceRange, flags, result);
    ASSERT(result.selectors.empty());
    unwrapResult(result);

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

void Lookup::unqualifiedImpl(const Scope& scope, string_view name, LookupLocation location,
                             SourceRange sourceRange, bitmask<LookupFlags> flags,
                             LookupResult& result) {
    // Try a simple name lookup to see if we find anything.
    auto& nameMap = scope.getNameMap();
    const Symbol* symbol = nullptr;
    if (auto it = nameMap.find(name); it != nameMap.end()) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the
        // scope, so the location doesn't matter for them.
        symbol = it->second;
        bool locationGood = true;
        if ((flags & LookupFlags::AllowDeclaredAfter) == 0) {
            locationGood = LookupLocation::before(*symbol) < location;
            if (!locationGood && symbol->kind == SymbolKind::TypeAlias) {
                // A type alias can have forward definitions, so check those locations as well.
                // The forward decls form a linked list that are always ordered by location,
                // so we only need to check the first one.
                const ForwardingTypedefSymbol* forward =
                    symbol->as<TypeAliasType>().getFirstForwardDecl();
                if (forward)
                    locationGood = LookupLocation::before(*forward) < location;
            }
        }

        if (locationGood) {
            // Unwrap the symbol if it's hidden behind an import or hoisted enum member.
            switch (symbol->kind) {
                case SymbolKind::ExplicitImport:
                    result.found = symbol->as<ExplicitImportSymbol>().importedSymbol();
                    result.wasImported = true;
                    break;
                case SymbolKind::TransparentMember:
                    result.found = &symbol->as<TransparentMemberSymbol>().wrapped;
                    break;
                case SymbolKind::ForwardingTypedef:
                    // If we find a forwarding typedef, the actual typedef was never defined.
                    // Just ignore it, we'll issue a better error later.
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
                    auto& diag = result.addDiag(scope, diag::RecursiveDefinition, sourceRange)
                                 << name;
                    diag.addNote(diag::NoteDeclarationHere, result.found->location);
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
            auto& diag = result.addDiag(scope, diag::AmbiguousWildcardImport, sourceRange) << name;
            for (const auto& pair : imports) {
                diag.addNote(diag::NoteImportedFrom, pair.import->location);
                diag.addNote(diag::NoteDeclarationHere, pair.imported->location);
            }
            return;
        }

        if (symbol) {
            auto& diag = result.addDiag(scope, diag::ImportNameCollision, sourceRange) << name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            diag.addNote(diag::NoteImportedFrom, imports[0].import->location);
            diag.addNote(diag::NoteDeclarationHere, imports[0].imported->location);
        }

        result.wasImported = true;
        result.found = imports[0].imported;
        return;
    }

    // Continue up the scope chain via our parent.
    location = LookupLocation::before(scope.asSymbol());
    if (!location.getScope())
        return;

    return unqualifiedImpl(*location.getScope(), name, location, sourceRange, flags, result);
}

void Lookup::qualified(const Scope& scope, const ScopedNameSyntax& syntax, LookupLocation location,
                       bitmask<LookupFlags> flags, LookupResult& result) {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    // TODO: clean up dot vs colon handling
    int colonParts = 0;
    SmallVectorSized<NamePlusLoc, 8> nameParts;
    const ScopedNameSyntax* scoped = &syntax;
    while (true) {
        nameParts.append({ scoped->right, scoped->separator.location() });
        if (scoped->separator.kind == TokenKind::Dot)
            colonParts = 0;
        else
            colonParts++;

        if (scoped->left->kind == SyntaxKind::ScopedName)
            scoped = &scoped->left->as<ScopedNameSyntax>();
        else
            break;
    }

    auto [nameToken, selectors] = decomposeName(*scoped->left);
    auto name = nameToken.valueText();
    if (name.empty())
        return;

    auto downward = [&, nameToken = nameToken, selectors = selectors]() {
        return lookupDownward(nameParts, nameToken, selectors, BindContext(scope, location), result,
                              flags);
    };

    auto& compilation = scope.getCompilation();
    if (compilation.isFinalizing())
        flags |= LookupFlags::Constant;

    bool inConstantEval = (flags & LookupFlags::Constant) != 0;

    switch (scoped->left->kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
            break;
        case SyntaxKind::UnitScope:
            result.found = getCompilationUnit(scope.asSymbol());
            downward();
            return;
        case SyntaxKind::RootScope:
            // Be careful to avoid calling getRoot() if we're in a constant context (there's a
            // chance we could already be in the middle of calling getRoot in that case).
            if (inConstantEval) {
                result.isHierarchical = true;
                result.addDiag(scope, diag::HierarchicalNotAllowedInConstant, nameToken.range());
                return;
            }

            result.found = &compilation.getRoot();
            downward();
            return;
        case SyntaxKind::ClassName:
        case SyntaxKind::LocalScope:
        case SyntaxKind::ThisHandle:
        case SyntaxKind::SuperHandle:
            result.addDiag(scope, diag::NotYetSupported, syntax.sourceRange());
            return;
        default:
            THROW_UNREACHABLE;
    }

    // Start by trying to find the first name segment using normal unqualified lookup
    unqualifiedImpl(scope, name, location, nameToken.range(), flags, result);
    if (result.hasError())
        return;

    // [23.7.1] If we are starting with a colon separator, always do a downwards name
    // resolution.
    if (colonParts) {
        // If the prefix name resolved normally to a class object, use that. Otherwise we need
        // to look for a package with the corresponding name.
        // TODO: handle the class scope check here

        result.found = compilation.getPackage(name);
        if (!result.found) {
            result.addDiag(scope, diag::UnknownClassOrPackage, nameToken.range()) << name;
            return;
        }

        // We can't do upwards name resolution if colon access is involved, so always return
        // after one downward lookup.
        downward();
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
        if (!downward())
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
        reportUndeclared(scope, name, nameToken.range(), flags, true, result);
        return;
    }

    // If we reach this point we're in case (2) or (4) above. Go up through the instantiation
    // hierarchy and see if we can find a match there.
    if (!lookupUpward(compilation, name, nameParts, nameToken, selectors,
                      BindContext(scope, location), result, flags)) {
        return;
    }
    if (result.found)
        return;

    // We couldn't find anything. originalResult has any diagnostics issued by the first
    // downward lookup (if any), so it's fine to just return it as is. If we never found any
    // symbol originally, issue an appropriate error for that.
    result.copyFrom(originalResult);
    if (!result.found && !result.hasError())
        reportUndeclared(scope, name, nameToken.range(), flags, true, result);
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
    // definition it's possible we haven't seen the file containing the package yet.
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
        auto isViable = [flags](const Symbol& sym) {
            if (flags & LookupFlags::Type)
                return sym.isType() || sym.kind == SymbolKind::TypeParameter;

            return sym.isValue() || sym.kind == SymbolKind::InstanceArray ||
                   (sym.kind == SymbolKind::Instance && sym.as<InstanceSymbol>().isInterface());
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
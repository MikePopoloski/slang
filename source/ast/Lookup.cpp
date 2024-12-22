//------------------------------------------------------------------------------
// Lookup.cpp
// Symbol lookup logic
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Lookup.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/ParserDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/SourceManager.h"
#include "slang/util/String.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const LookupLocation LookupLocation::max{nullptr, UINT_MAX};
const LookupLocation LookupLocation::min{nullptr, 0};

LookupLocation LookupLocation::before(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex());
}

LookupLocation LookupLocation::after(const Symbol& symbol) {
    return LookupLocation(symbol.getParentScope(), (uint32_t)symbol.getIndex() + 1);
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceLocation location) {
    return diagnostics.add(scope.asSymbol(), code, location);
}

Diagnostic& LookupResult::addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange) {
    return diagnostics.add(scope.asSymbol(), code, sourceRange);
}

bool LookupResult::hasError() const {
    // We have an error if we have any diagnostics or if there was a missing explicit import.
    if (!found && flags.has(LookupResultFlags::WasImported | LookupResultFlags::SuppressUndeclared))
        return true;

    for (auto& diag : diagnostics) {
        if (diag.isError())
            return true;
    }

    return false;
}

void LookupResult::clear() {
    found = nullptr;
    systemSubroutine = nullptr;
    upwardCount = 0;
    flags = LookupResultFlags::None;
    selectors.clear();
    path.clear();
    diagnostics.clear();
}

void LookupResult::reportDiags(const ASTContext& context) const {
    context.getCompilation().addDiagnostics(diagnostics);
}

void LookupResult::errorIfSelectors(const ASTContext& context) const {
    if (selectors.empty())
        return;

    SourceRange range;
    auto& sel = selectors[0];
    if (sel.index() == 0)
        range = std::get<0>(sel)->sourceRange();
    else
        range = std::get<1>(sel).nameRange;

    context.addDiag(diag::UnexpectedSelection, range);
}

namespace {

struct NameComponents {
    std::string_view text;
    SourceRange range;
    std::span<const ElementSelectSyntax* const> selectors;
    const ParameterValueAssignmentSyntax* paramAssignments = nullptr;

    NameComponents() = default;
    NameComponents(const NameSyntax& name) {
        switch (name.kind) {
            case SyntaxKind::IdentifierName:
                set(name.as<IdentifierNameSyntax>().identifier);
                break;
            case SyntaxKind::SystemName:
                set(name.as<SystemNameSyntax>().systemIdentifier);
                break;
            case SyntaxKind::IdentifierSelectName: {
                auto& idSelect = name.as<IdentifierSelectNameSyntax>();
                set(idSelect.identifier);
                selectors = idSelect.selectors;
                break;
            }
            case SyntaxKind::ClassName: {
                auto& cn = name.as<ClassNameSyntax>();
                set(cn.identifier);
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
                set(name.as<KeywordNameSyntax>().keyword);
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    void set(Token id) {
        text = id.valueText();
        range = id.range();
    }
};

struct NamePlusLoc {
    NameComponents name;
    SourceLocation dotLocation;
    SyntaxKind kind;
};

const Symbol* unwrapTypeParam(const Scope& scope, const Symbol* symbol) {
    if (symbol->kind == SymbolKind::TypeParameter) {
        scope.getCompilation().noteReference(*symbol);

        auto result = &symbol->as<TypeParameterSymbol>().targetType.getType();
        if (result->isError())
            return nullptr;

        return result;
    }
    return symbol;
}

std::optional<bool> isClassType(const Symbol& symbol) {
    if (symbol.isType()) {
        auto& type = symbol.as<Type>();
        if (type.isError())
            return std::nullopt;

        return type.isClass();
    }

    return symbol.kind == SymbolKind::GenericClassDef;
}

const NameSyntax* splitScopedName(const ScopedNameSyntax& syntax,
                                  SmallVectorBase<NamePlusLoc>& nameParts, int& colonParts) {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    const ScopedNameSyntax* scoped = &syntax;
    while (true) {
        nameParts.push_back({*scoped->right, scoped->separator.location(), scoped->right->kind});
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

const Symbol* getVirtualInterfaceTarget(const Type& type, const ASTContext& context,
                                        SourceRange range) {
    if (context.flags.has(ASTFlags::NonProcedural))
        context.addDiag(diag::DynamicNotProcedural, range);

    auto& vit = type.getCanonicalType().as<VirtualInterfaceType>();
    if (vit.modport)
        return vit.modport;

    return &vit.iface;
}

bool isInProgram(const Symbol& symbol) {
    auto curr = &symbol;
    while (true) {
        if (curr->kind == SymbolKind::AnonymousProgram)
            return true;

        if (curr->kind == SymbolKind::InstanceBody) {
            return curr->as<InstanceBodySymbol>().getDefinition().definitionKind ==
                   DefinitionKind::Program;
        }

        auto scope = curr->getParentScope();
        if (!scope)
            return false;

        curr = &scope->asSymbol();
    }
}

const Symbol* getContainingPackage(const Symbol& symbol) {
    auto curr = &symbol;
    while (true) {
        if (curr->kind == SymbolKind::Package)
            return curr;

        if (curr->kind == SymbolKind::InstanceBody)
            return nullptr;

        auto scope = curr->getParentScope();
        if (!scope)
            return nullptr;

        curr = &scope->asSymbol();
    }
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupDownward(std::span<const NamePlusLoc> nameParts, NameComponents name,
                    const ASTContext& context, bitmask<LookupFlags> flags, LookupResult& result) {
    const Symbol* symbol = std::exchange(result.found, nullptr);
    SLANG_ASSERT(symbol);

    // Helper function to check whether class parameter assignments have been
    // incorrectly supplied for a non-class symbol.
    auto checkClassParams = [&](const NameComponents& nc) {
        if (symbol && symbol->kind != SymbolKind::GenericClassDef && nc.paramAssignments) {
            auto& diag = result.addDiag(*context.scope, diag::NotAGenericClass,
                                        nc.paramAssignments->getFirstToken().location());
            diag << nc.range;
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return false;
        }
        return true;
    };

    // Loop through each dotted name component and try to find it in the preceeding scope.
    bool isVirtualIface = false;
    for (auto it = nameParts.rbegin(); it != nameParts.rend(); it++) {
        if (!checkClassParams(name))
            return false;

        auto isValueLike = [&](const Symbol*& symbol) {
            switch (symbol->kind) {
                case SymbolKind::ConstraintBlock:
                case SymbolKind::Coverpoint:
                case SymbolKind::CoverCross:
                case SymbolKind::Sequence:
                case SymbolKind::Property:
                case SymbolKind::LetDecl:
                case SymbolKind::AssertionPort:
                    return true;
                default: {
                    if (!symbol->isValue())
                        return false;

                    // If this is a virtual interface value we should unwrap to
                    // the target interface and continue the hierarchical lookup.
                    auto& type = symbol->as<ValueSymbol>().getType();
                    if (type.isVirtualInterface()) {
                        isVirtualIface = true;
                        context.getCompilation().noteReference(*symbol);
                        symbol = getVirtualInterfaceTarget(type, context, name.range);
                        return false;
                    }

                    return true;
                }
            }
        };

        // If we found a value, the remaining dots are member access expressions.
        if (isValueLike(symbol)) {
            result.selectors.append_range(name.selectors);

            for (; it != nameParts.rend(); it++) {
                auto& memberName = it->name;
                result.selectors.push_back(LookupResult::MemberSelector{
                    memberName.text, it->dotLocation, memberName.range});

                result.selectors.append_range(memberName.selectors);

                if (!checkClassParams(memberName))
                    return false;
            }

            // Break out to return the symbol.
            name.selectors = {};
            break;
        }

        // This is a hierarchical lookup if we previously decided it was hierarchical, or:
        // - This is not a clocking block access
        // - This is not a virtual interface access (or descended from one)
        // - This is not a direct interface port, package, or $unit reference
        const bool isCBOrVirtualIface = symbol->kind == SymbolKind::ClockingBlock || isVirtualIface;
        if (it == nameParts.rbegin()) {
            if (symbol->kind != SymbolKind::InterfacePort && symbol->kind != SymbolKind::Package &&
                symbol->kind != SymbolKind::CompilationUnit && !isCBOrVirtualIface) {
                result.flags |= LookupResultFlags::IsHierarchical;
                result.path.emplace_back(*symbol);
            }
        }
        else if (flags.has(LookupFlags::IfacePortConn) &&
                 (symbol->kind == SymbolKind::GenerateBlock ||
                  symbol->kind == SymbolKind::GenerateBlockArray ||
                  symbol->kind == SymbolKind::InstanceArray)) {
            SourceRange errorRange{name.range.start(), (nameParts.rend() - 1)->name.range.end()};
            result.addDiag(*context.scope, diag::InvalidHierarchicalIfacePortConn, errorRange);
            return false;
        }
        else if (!isCBOrVirtualIface) {
            result.flags |= LookupResultFlags::IsHierarchical;
            result.path.emplace_back(*symbol);
        }

        const ModportSymbol* modport = nullptr;
        if (symbol->kind == SymbolKind::InterfacePort) {
            auto& ifacePort = symbol->as<InterfacePortSymbol>();
            std::tie(symbol, modport) = ifacePort.getConnection();
            if (!symbol)
                return false;
        }

        if ((!symbol->isScope() && symbol->kind != SymbolKind::Instance) || symbol->isType() ||
            symbol->kind == SymbolKind::Checker) {
            // If we found an uninstantiated def, exit silently. An appropriate error was
            // already issued, so no need to pile on.
            if (symbol->kind == SymbolKind::UninstantiatedDef)
                return false;

            symbol = unwrapTypeParam(*context.scope, symbol);
            if (!symbol)
                return false;

            bool isType;
            if (symbol->isType()) {
                isType = true;
                if (symbol->as<Type>().isError())
                    return false;
            }
            else {
                isType = symbol->kind == SymbolKind::GenericClassDef;
            }

            DiagCode code;
            if (isType) {
                code = diag::DotOnType;
            }
            else if (symbol->kind == SymbolKind::Checker ||
                     symbol->kind == SymbolKind::CheckerInstance) {
                code = diag::CheckerHierarchical;
            }
            else {
                code = diag::NotAHierarchicalScope;
            }

            auto& diag = result.addDiag(*context.scope, code, it->dotLocation);
            diag << name.range;
            diag << it->name.range;

            if (!isType)
                diag << name.text;

            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return true;
        }

        if (!name.selectors.empty()) {
            symbol = Lookup::selectChild(*symbol, name.selectors, context, result);
            if (!symbol)
                return false;
        }

        if (symbol->kind == SymbolKind::Instance) {
            auto& body = symbol->as<InstanceSymbol>().body;
            symbol = &body;

            // If we had a modport restriction on an interface port lookup
            // we should switch to doing the next lookup in that modport's scope.
            // We need to re-lookup the modport symbol because the one we have
            // is just representative; the real one depends on the result of the
            // selectChild call we made above in the case of an interface array.
            if (modport) {
                symbol = body.find(modport->name);
                SLANG_ASSERT(symbol);
            }

            // If we're descending into a program instance, verify that
            // the original scope for the lookup is also within a program.
            if (body.getDefinition().definitionKind == DefinitionKind::Program &&
                !isInProgram(context.scope->asSymbol())) {
                SourceRange errorRange{name.range.start(),
                                       (nameParts.rend() - 1)->name.range.end()};
                result.addDiag(*context.scope, diag::IllegalReferenceToProgramItem, errorRange);
            }
        }
        else if (symbol->kind == SymbolKind::GenerateBlock &&
                 symbol->as<GenerateBlockSymbol>().isUninstantiated) {
            // Don't allow lookups into uninstantiated generate blocks, but do return
            // true so that the lookup can continue elsewhere.
            return true;
        }

        name = it->name;
        if (name.text.empty())
            return false;

        auto& scope = symbol->as<Scope>();
        symbol = scope.find(name.text);
        if (!symbol) {
            // If we did the lookup in a modport, check to see if the symbol actually
            // exists in the parent interface.
            auto& prevSym = scope.asSymbol();
            if (prevSym.kind != SymbolKind::Modport ||
                (symbol = prevSym.getParentScope()->find(name.text)) == nullptr) {

                // Check if we actually had a method prototype found here but it failed
                // to resolve due to some other error, in which case we should keep quiet.
                auto& nameMap = scope.getNameMap();
                if (auto scopeIt = nameMap.find(name.text);
                    scopeIt != nameMap.end() &&
                    scopeIt->second->kind == SymbolKind::MethodPrototype) {
                    return false;
                }

                // Which error we report depends on whether this is an array
                // (in which case the user needs to use an index expression instead
                // of dot access) or just some other symbol that is missing the
                // requested member.
                if (prevSym.kind == SymbolKind::GenerateBlockArray ||
                    prevSym.kind == SymbolKind::InstanceArray) {
                    result.addDiag(*context.scope, diag::DotIntoInstArray, it->dotLocation);
                }
                else {
                    auto& diag = result.addDiag(*context.scope,
                                                diag::CouldNotResolveHierarchicalPath,
                                                it->dotLocation);
                    diag << name.text;
                    diag << name.range;
                }
                return true;
            }

            // Variables, nets, subroutines can only be accessed via the modport.
            // Other symbols aren't permitted in a modport, so they are allowed
            // to be accessed through it as if we had accessed the interface
            // instance itself.
            if (SemanticFacts::isAllowedInModport(symbol->kind) ||
                symbol->kind == SymbolKind::Modport) {
                // This is an error, the modport disallows access.
                auto def = prevSym.getDeclaringDefinition();
                SLANG_ASSERT(def);

                auto& diag = result.addDiag(*context.scope, diag::InvalidModportAccess, name.range);
                diag << name.text;
                diag << def->name;
                diag << prevSym.name;
                return false;
            }
        }
    }

    if (!checkClassParams(name))
        return false;

    if (result.flags.has(LookupResultFlags::IsHierarchical) && symbol) {
        if (VariableSymbol::isKind(symbol->kind) &&
            symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            // If we found an automatic variable check that we didn't try to reference it
            // hierarchically.
            result.addDiag(*context.scope, diag::AutoVariableHierarchical, name.range);
            return false;
        }
        else if (symbol->isType()) {
            // Types cannot be referenced hierarchically.
            result.addDiag(*context.scope, diag::TypeHierarchical, name.range);
            return false;
        }
        result.path.emplace_back(*symbol);
    }

    result.found = symbol;

    if (!name.selectors.empty()) {
        // If this is a scope, the selectors should be an index into it.
        if (result.found && result.found->isScope() && !result.found->isType())
            result.found = Lookup::selectChild(*result.found, name.selectors, context, result);
        else
            result.selectors.append_range(name.selectors);
    }

    return true;
}

// Returns true if the lookup was ok, or if it failed in a way that allows us to continue
// looking up in other ways. Returns false if the entire lookup has failed and should be
// aborted.
bool lookupUpward(std::span<const NamePlusLoc> nameParts, const NameComponents& name,
                  const ASTContext& context, bitmask<LookupFlags> flags, LookupResult& result) {
    // Upward lookups can match either a scope name, or a module definition name (on any of the
    // instances). Imports are not considered.
    const Symbol* firstMatch = nullptr;
    auto tryMatch = [&](const Symbol& symbol) {
        // Keep track of the first match we find; if it turns out we can't
        // resolve all of the name parts we'll move on and try elsewhere,
        // but at the end if we couldn't find a full match we'll use this to
        // provide a better error.
        if (!firstMatch)
            firstMatch = &symbol;

        result.clear();
        result.found = &symbol;
        return lookupDownward(nameParts, name, context, flags, result);
    };

    uint32_t upwardCount = 0;
    const Scope* scope = context.scope;
    do {
        // Search for a scope or instance target within our current scope.
        auto symbol = scope->find(name.text);
        if (symbol && !symbol->isValue() && !symbol->isType() &&
            (symbol->isScope() || symbol->kind == SymbolKind::Instance)) {
            if (!tryMatch(*symbol))
                return false;

            if (result.found) {
                result.upwardCount = upwardCount;
                return true;
            }
        }

        // Advance to the next scope, skipping to the parent instance when
        // we hit an instance body instead of going on to the compilation unit.
        symbol = &scope->asSymbol();
        if (symbol->kind != SymbolKind::InstanceBody) {
            scope = symbol->getHierarchicalParent();
        }
        else {
            auto inst = symbol->as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(inst);

            // If the instance's definition name matches our target name,
            // try to match from the current instance.
            scope = inst->getParentScope();
            if (inst->getDefinition().name == name.text) {
                if (!tryMatch(*inst))
                    return false;

                if (result.found) {
                    result.upwardCount = upwardCount;
                    return true;
                }
            }
        }

        upwardCount++;
    } while (scope);

    result.clear();
    if (firstMatch) {
        // If we did find a match at some point, repeat that
        // lookup to provide a real error message.
        result.found = firstMatch;
        lookupDownward(nameParts, name, context, flags, result);
        return false;
    }
    return true;
}

bool checkVisibility(const Symbol& symbol, const Scope& scope,
                     std::optional<SourceRange> sourceRange, LookupResult& result) {
    // All public members and all non-class symbols are visible by default.
    Visibility visibility = Lookup::getVisibility(symbol);
    if (visibility == Visibility::Public)
        return true;

    // All non-public members can only be accessed from scopes that are within a class.
    auto [lp, _] = Lookup::getContainingClass(scope);
    const Symbol& targetParent = symbol.getParentScope()->asSymbol();

    const Symbol* lookupParent = lp;
    if (lookupParent && targetParent.kind == SymbolKind::ClassType) {
        auto genericTarget = targetParent.as<ClassType>().genericClass;
        if (visibility == Visibility::Local) {
            // Local members can only be accessed from the declaring class,
            // or from any nested classes within that class.
            do {
                if (lookupParent == &targetParent)
                    return true;

                if (genericTarget && lookupParent->as<ClassType>().genericClass == genericTarget)
                    return true;

                lookupParent = &lookupParent->getParentScope()->asSymbol();
            } while (lookupParent->kind == SymbolKind::ClassType);
        }
        else {
            // Protected members can be accessed from derived classes as well,
            // in addition to nested classes within those derived classes.
            auto& targetType = targetParent.as<Type>();
            do {
                auto& sourceType = lookupParent->as<ClassType>();
                if (targetType.isAssignmentCompatible(sourceType))
                    return true;

                if (genericTarget && sourceType.genericClass == genericTarget)
                    return true;

                lookupParent = &lookupParent->getParentScope()->asSymbol();
            } while (lookupParent->kind == SymbolKind::ClassType);
        }
    }

    if (sourceRange) {
        if (symbol.kind == SymbolKind::Subroutine &&
            symbol.as<SubroutineSymbol>().flags.has(MethodFlags::Constructor)) {

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

bool resolveColonNames(SmallVectorBase<NamePlusLoc>& nameParts, int colonParts,
                       NameComponents& name, bitmask<LookupFlags> flags, LookupResult& result,
                       const ASTContext& context) {
    // Unwrap the symbol if it's a type parameter, and bail early if it's an error type.
    const Symbol* symbol = std::exchange(result.found, nullptr);
    if (symbol) {
        symbol = unwrapTypeParam(*context.scope, symbol);
        if (!symbol)
            return false;
    }

    auto isCovergroup = [&](const Symbol& symbol) {
        switch (symbol.kind) {
            case SymbolKind::Coverpoint:
            case SymbolKind::CoverCross:
                return true;
            default:
                return symbol.isType() && symbol.as<Type>().isCovergroup();
        }
    };

    // If the prefix name resolved normally to a class object, use that. Otherwise we need
    // to look for a package with the corresponding name.
    bool lookForPackage = symbol == nullptr;
    if (symbol) {
        auto isClass = isClassType(*symbol);
        if (!isClass.has_value())
            return false;

        lookForPackage = !isClass.value() && !isCovergroup(*symbol);
    }

    if (lookForPackage) {
        symbol = context.getCompilation().getPackage(name.text);
        if (!symbol) {
            if (!context.scope->isUninstantiated()) {
                result.addDiag(*context.scope, diag::UnknownClassOrPackage, name.range)
                    << name.text;
            }
            return false;
        }
    }

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
                auto [parent, _] = Lookup::getContainingClass(*context.scope);
                if (!parent || parent->genericClass != symbol) {
                    result.addDiag(*context.scope, diag::GenericClassScopeResolution, name.range);
                    return false;
                }
                symbol = parent;
            }
        }
        else if (name.paramAssignments) {
            auto& diag = result.addDiag(*context.scope, diag::NotAGenericClass, name.range);
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return false;
        }

        // If this is a type alias, check its visibility.
        checkVisibility(*symbol, *context.scope, name.range, result);

        return true;
    };

    while (colonParts--) {
        if (!name.selectors.empty()) {
            Token first = name.selectors.front()->getFirstToken();
            Token last = name.selectors.back()->getLastToken();

            result.addDiag(*context.scope, diag::InvalidScopeIndexExpression,
                           {first.location(), last.location()});
            return false;
        }

        auto& part = nameParts.back();
        symbol = unwrapTypeParam(*context.scope, symbol);
        if (!symbol)
            return false;

        if (symbol->kind != SymbolKind::Package) {
            auto isClass = isClassType(*symbol);
            if (!isClass.has_value())
                return false;

            if (!isClass.value() && !isCovergroup(*symbol)) {
                auto& diag = result.addDiag(*context.scope, diag::NotAClass, part.dotLocation);
                diag << name.range;
                diag << symbol->name;
                diag.addNote(diag::NoteDeclarationHere, symbol->location);
                return false;
            }
        }

        if (!validateSymbol())
            return false;

        name = part.name;
        if (name.text.empty())
            return false;

        if (symbol->isType()) {
            if (symbol->kind == SymbolKind::TypeAlias)
                context.getCompilation().noteReference(*symbol);

            symbol = &symbol->as<Type>().getCanonicalType();
        }

        const Symbol* savedSymbol = symbol;
        if (symbol->kind == SymbolKind::Package) {
            symbol = symbol->as<PackageSymbol>().findForImport(name.text);
            result.flags |= LookupResultFlags::WasImported;
        }
        else if (symbol->kind == SymbolKind::CovergroupType) {
            symbol = symbol->as<CovergroupType>().getBody().find(name.text);
        }
        else {
            symbol = symbol->as<Scope>().find(name.text);
        }

        if (!symbol) {
            DiagCode code = diag::UnknownClassMember;
            if (savedSymbol->kind == SymbolKind::Package)
                code = diag::UnknownPackageMember;
            else if (savedSymbol->kind == SymbolKind::CovergroupType)
                code = diag::UnknownCovergroupMember;

            auto& diag = result.addDiag(*context.scope, code, part.dotLocation);
            diag << name.text;
            diag << name.range;
            diag << savedSymbol->name;
            return false;
        }

        nameParts.pop_back();
    }

    if (!validateSymbol())
        return false;

    // The initial symbol found cannot be resolved via a forward typedef (i.e. "incomplete")
    // unless this is within a typedef declaration.
    if (result.flags.has(LookupResultFlags::FromForwardTypedef) &&
        !flags.has(LookupFlags::AllowIncompleteForwardTypedefs) && symbol->isType()) {
        result.flags &= ~LookupResultFlags::FromForwardTypedef;
        result.addDiag(*context.scope, diag::ScopeIncompleteTypedef, name.range);
    }

    result.found = symbol;
    return lookupDownward(nameParts, name, context, flags, result);
}

void unwrapResult(const Scope& scope, std::optional<SourceRange> range, LookupResult& result,
                  bool unwrapGenericClasses = true) {
    if (!result.found)
        return;

    if (result.flags.has(LookupResultFlags::IsHierarchical)) {
        auto declaredType = result.found->getDeclaredType();
        if (declaredType && declaredType->isEvaluating()) {
            if (range) {
                auto& diag = result.addDiag(scope, diag::RecursiveDefinition, *range);
                diag << result.found->name;
                diag.addNote(diag::NoteDeclarationHere, result.found->location);
            }
            result.found = nullptr;
            return;
        }
    }

    checkVisibility(*result.found, scope, range, result);

    // Unwrap type parameters into their target type alias.
    if (result.found->kind == SymbolKind::TypeParameter) {
        scope.getCompilation().noteReference(*result.found);

        result.found = &result.found->as<TypeParameterSymbol>().getTypeAlias();
        result.flags |= LookupResultFlags::FromTypeParam;
    }
    else if (result.found->kind == SymbolKind::TypeAlias) {
        scope.getCompilation().noteReference(*result.found);
    }

    // If the found symbol is a generic class, unwrap into
    // the default specialization (if possible).
    if (result.found->kind == SymbolKind::GenericClassDef && unwrapGenericClasses) {
        auto& genericClass = result.found->as<GenericClassDefSymbol>();
        result.found = genericClass.getDefaultSpecialization();

        if (!result.found) {
            if (range)
                result.addDiag(scope, diag::NoDefaultSpecialization, *range) << genericClass.name;
            return;
        }
    }

    if (!range)
        return;

    if (result.flags.has(LookupResultFlags::WasImported)) {
        // If the symbol was imported from a package, check if it is actually
        // declared within an anonymous program within that package and if so,
        // check whether we're allowed to reference it from our source scope.
        auto parent = result.found->getParentScope();
        while (parent) {
            auto& parentSym = parent->asSymbol();
            if (parentSym.kind == SymbolKind::Package)
                break;

            if (parentSym.kind == SymbolKind::AnonymousProgram) {
                if (!isInProgram(scope.asSymbol())) {
                    auto& diag = result.addDiag(scope, diag::IllegalReferenceToProgramItem, *range);
                    diag.addNote(diag::NoteDeclarationHere, result.found->location);
                }
                break;
            }

            parent = parentSym.getParentScope();
        }
    }
    else if (result.flags.has(LookupResultFlags::IsHierarchical)) {
        // Hierarchical references are not allowed from within packages
        // unless the target symbol is also within the same package.
        auto pkg = getContainingPackage(scope.asSymbol());
        if (pkg && getContainingPackage(*result.found) != pkg)
            result.addDiag(scope, diag::HierarchicalFromPackage, *range);
    }
    else if (auto parent = result.found->getParentScope();
             parent && parent->asSymbol().kind == SymbolKind::CompilationUnit) {
        // Compilation unit items are not allowed to be referenced from a package.
        if (getContainingPackage(scope.asSymbol())) {
            auto& diag = result.addDiag(scope, diag::CompilationUnitFromPackage, *range);
            diag.addNote(diag::NoteDeclarationHere, result.found->location);
        }
    }
}

const Symbol* findThisHandle(const Scope& scope, bitmask<LookupFlags> flags, SourceRange range,
                             LookupResult& result) {
    if (flags.has(LookupFlags::TypeReference)) {
        // type(this) is allowed to work anywhere within a class, regardless of whether
        // it's a static context or not.
        auto parent = &scope.asSymbol();
        while (parent->kind != SymbolKind::ClassType && parent->kind != SymbolKind::InstanceBody) {
            auto parentScope = parent->getParentScope();
            if (!parentScope)
                break;
            parent = &parentScope->asSymbol();
        }

        if (parent->kind == SymbolKind::ClassType)
            return &parent->as<ClassType>();
    }
    else {
        // Find the parent method, if we can.
        const Symbol* parent = &scope.asSymbol();
        while (parent->kind == SymbolKind::StatementBlock ||
               parent->kind == SymbolKind::RandSeqProduction) {
            auto parentScope = parent->getParentScope();
            SLANG_ASSERT(parentScope);
            parent = &parentScope->asSymbol();
        }

        if (parent->kind == SymbolKind::Subroutine) {
            auto& sub = parent->as<SubroutineSymbol>();
            if (sub.thisVar)
                return sub.thisVar;
        }
        else if (parent->kind == SymbolKind::ConstraintBlock) {
            auto thisVar = parent->as<ConstraintBlockSymbol>().thisVar;
            if (thisVar)
                return thisVar;
        }
        else if (parent->kind == SymbolKind::ClassType &&
                 !flags.has(LookupFlags::StaticInitializer)) {
            return parent->as<ClassType>().thisVar;
        }
    }

    result.addDiag(scope, diag::InvalidThisHandle, range);
    return nullptr;
}

const Symbol* findSuperHandle(const Scope& scope, bitmask<LookupFlags> flags, SourceRange range,
                              LookupResult& result) {
    auto [parent, inStatic] = Lookup::getContainingClass(scope);
    if (!parent) {
        result.addDiag(scope, diag::SuperOutsideClass, range);
        return nullptr;
    }

    if (inStatic || flags.has(LookupFlags::StaticInitializer)) {
        result.addDiag(scope, diag::NonStaticClassProperty, range) << "super"sv;
        return nullptr;
    }

    auto base = parent->getBaseClass();
    if (!base && !parent->name.empty()) {
        result.addDiag(scope, diag::SuperNoBase, range) << parent->name;
        return nullptr;
    }

    return base;
}

bool withinCovergroup(const Symbol& symbol, const Scope& initialScope) {
    const Scope* nextScope = &initialScope;
    do {
        switch (nextScope->asSymbol().kind) {
            case SymbolKind::CovergroupType:
            case SymbolKind::CovergroupBody:
            case SymbolKind::Coverpoint:
            case SymbolKind::CoverCross:
                if (symbol.getParentScope() == nextScope)
                    return true;

                nextScope = nextScope->asSymbol().getParentScope();
                break;
            default:
                nextScope = nullptr;
                break;
        }
    } while (nextScope);

    return false;
}

} // namespace

void Lookup::name(const NameSyntax& syntax, const ASTContext& context, bitmask<LookupFlags> flags,
                  LookupResult& result) {
    auto& scope = *context.scope;
    NameComponents name;
    switch (syntax.kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            name = syntax;
            break;
        case SyntaxKind::ScopedName:
            // Handle qualified names separately.
            qualified(syntax.as<ScopedNameSyntax>(), context, flags, result);
            unwrapResult(scope, syntax.sourceRange(), result);
            if (flags.has(LookupFlags::NoSelectors))
                result.errorIfSelectors(context);
            return;
        case SyntaxKind::ThisHandle:
            result.found = findThisHandle(scope, flags, syntax.sourceRange(), result);
            return;
        case SyntaxKind::SystemName: {
            // If this is a system name, look up directly in the compilation.
            Token nameToken = syntax.as<SystemNameSyntax>().systemIdentifier;
            result.found = nullptr;
            result.systemSubroutine = scope.getCompilation().getSystemSubroutine(
                nameToken.valueText());

            if (!result.systemSubroutine) {
                result.addDiag(scope, diag::UnknownSystemName, nameToken.range())
                    << nameToken.valueText();
            }
            return;
        }
        case SyntaxKind::RootScope:
            if (!flags.has(LookupFlags::AllowRoot)) {
                auto tok = syntax.getFirstToken();
                result.addDiag(scope, diag::ExpectedToken,
                               tok.location() + tok.valueText().length())
                    << "."sv;
                return;
            }
            result.found = &scope.getCompilation().getRoot();
            return;
        case SyntaxKind::UnitScope:
            if (!flags.has(LookupFlags::AllowUnit)) {
                auto tok = syntax.getFirstToken();
                result.addDiag(scope, diag::ExpectedToken,
                               tok.location() + tok.valueText().length())
                    << "::"sv;
                return;
            }
            result.found = scope.getCompilationUnit();
            return;
        case SyntaxKind::ConstructorName:
            result.addDiag(scope, diag::UnexpectedNameToken, syntax.sourceRange())
                << syntax.getFirstToken().valueText();
            result.found = nullptr;
            return;
        case SyntaxKind::LocalScope:
            // This can only happen in error scenarios, where the parser has
            // already issued a diagnostic.
            result.found = nullptr;
            return;
        case SyntaxKind::SuperHandle:
        case SyntaxKind::ArrayUniqueMethod:
        case SyntaxKind::ArrayAndMethod:
        case SyntaxKind::ArrayOrMethod:
        case SyntaxKind::ArrayXorMethod:
            // These error cases can't happen here because the parser will always
            // wrap them into a scoped name.
        default:
            SLANG_UNREACHABLE;
    }

    // If the parser added a missing identifier token, it already issued an appropriate error.
    if (name.text.empty())
        return;

    // Perform the lookup.
    unqualifiedImpl(scope, name.text, context.getLocation(), name.range, flags, {}, result, scope,
                    &syntax);

    if (!result.found) {
        if (flags.has(LookupFlags::AlwaysAllowUpward)) {
            if (!lookupUpward({}, name, context, flags, result))
                return;
        }

        if (!result.found && !result.hasError())
            reportUndeclared(scope, name.text, name.range, flags, false, result);
    }

    if (result.found && name.paramAssignments) {
        if (result.found->kind != SymbolKind::GenericClassDef) {
            auto& diag = result.addDiag(scope, diag::NotAGenericClass, syntax.sourceRange());
            diag << result.found->name;
            diag.addNote(diag::NoteDeclarationHere, result.found->location);

            result.found = nullptr;
        }
        else {
            auto& classDef = result.found->as<GenericClassDefSymbol>();
            result.found = &classDef.getSpecialization(context, *name.paramAssignments);
        }
    }

    unwrapResult(scope, syntax.sourceRange(), result);

    if (!name.selectors.empty()) {
        // If this is a scope, the selectors should be an index into it.
        if (result.found && result.found->isScope() && !result.found->isType()) {
            result.found = selectChild(*result.found, name.selectors, context, result);
        }
        else {
            result.selectors.append_range(name.selectors);
            if (flags.has(LookupFlags::NoSelectors))
                result.errorIfSelectors(context);
        }
    }
}

const Symbol* Lookup::unqualified(const Scope& scope, std::string_view name,
                                  bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, LookupLocation::max, std::nullopt, flags, {}, result, scope,
                    nullptr);

    SLANG_ASSERT(result.selectors.empty());
    unwrapResult(scope, std::nullopt, result, /* unwrapGenericClasses */ false);

    return result.found;
}

const Symbol* Lookup::unqualifiedAt(const Scope& scope, std::string_view name,
                                    LookupLocation location, SourceRange sourceRange,
                                    bitmask<LookupFlags> flags) {
    if (name.empty())
        return nullptr;

    LookupResult result;
    unqualifiedImpl(scope, name, location, sourceRange, flags, {}, result, scope, nullptr);

    SLANG_ASSERT(result.selectors.empty());
    unwrapResult(scope, sourceRange, result, /* unwrapGenericClasses */ false);

    if (!result.found && !result.hasError())
        reportUndeclared(scope, name, sourceRange, flags, false, result);

    if (result.hasError())
        scope.getCompilation().addDiagnostics(result.getDiagnostics());

    return result.found;
}

static const Symbol* selectSingleChild(const Symbol& symbol, const BitSelectSyntax& syntax,
                                       const ASTContext& context, LookupResult& result) {
    auto index = context.evalInteger(*syntax.expr);
    if (!index)
        return nullptr;

    if (symbol.kind == SymbolKind::InstanceArray) {
        auto& array = symbol.as<InstanceArraySymbol>();
        if (array.elements.empty())
            return nullptr;

        if (!array.range.containsPoint(*index)) {
            auto& diag = result.addDiag(*context.scope, diag::ScopeIndexOutOfRange,
                                        syntax.sourceRange());
            diag << *index;
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
            return nullptr;
        }

        auto child = array.elements[size_t(array.range.translateIndex(*index))];
        result.path.emplace_back(*child, *index);
        return child;
    }
    else {
        auto& array = symbol.as<GenerateBlockArraySymbol>();
        if (!array.valid)
            return nullptr;

        for (auto entry : array.entries) {
            if (entry->arrayIndex && *entry->arrayIndex == *index) {
                result.path.emplace_back(*entry, *index);
                return entry;
            }
        }

        auto& diag = result.addDiag(*context.scope, diag::ScopeIndexOutOfRange,
                                    syntax.sourceRange());
        diag << *index;
        diag.addNote(diag::NoteDeclarationHere, symbol.location);
        return nullptr;
    }
}

static const Symbol* selectChildRange(const InstanceArraySymbol& array,
                                      const RangeSelectSyntax& syntax, const ASTContext& context,
                                      LookupResult& result) {
    if (array.elements.empty())
        return nullptr;

    // Evaluate both sides of the range.
    auto left = context.evalInteger(*syntax.left);
    auto right = context.evalInteger(*syntax.right);
    if (!left || !right)
        return nullptr;

    ConstantRange selRange;
    if (syntax.kind == SyntaxKind::SimpleRangeSelect) {
        selRange = {*left, *right};
        if (selRange.isLittleEndian() != array.range.isLittleEndian() && selRange.width() > 1) {
            auto& diag = result.addDiag(*context.scope, diag::InstanceArrayEndianMismatch,
                                        syntax.sourceRange());
            diag << selRange.left << selRange.right;
            diag << array.range.left << array.range.right;
            return nullptr;
        }
    }
    else {
        if (*right <= 0) {
            result.addDiag(*context.scope, diag::ValueMustBePositive, syntax.right->sourceRange());
            return nullptr;
        }

        auto range = ConstantRange::getIndexedRange(*left, *right, array.range.isLittleEndian(),
                                                    syntax.kind ==
                                                        SyntaxKind::AscendingRangeSelect);
        if (!range) {
            result.addDiag(*context.scope, diag::RangeWidthOverflow, syntax.sourceRange());
            return nullptr;
        }

        selRange = *range;
    }

    if (!array.range.containsPoint(selRange.left) || !array.range.containsPoint(selRange.right)) {
        auto& diag = result.addDiag(*context.scope, diag::BadInstanceArrayRange,
                                    syntax.sourceRange());
        diag << selRange.left << selRange.right;
        diag << array.range.left << array.range.right;
        return nullptr;
    }

    int32_t begin = array.range.translateIndex(selRange.left);
    int32_t end = array.range.translateIndex(selRange.right);
    if (begin > end)
        std::swap(begin, end);

    auto elems = array.elements.subspan(size_t(begin), size_t(end - begin) + 1);

    ConstantRange newRange{int32_t(selRange.width()) - 1, 0};
    if (!selRange.isLittleEndian())
        newRange = newRange.reverse();

    // Create a placeholder array symbol that will hold this new sliced array.
    auto& comp = context.getCompilation();
    auto children = comp.emplace<InstanceArraySymbol>(comp, ""sv, syntax.getFirstToken().location(),
                                                      elems, newRange);
    result.path.emplace_back(*children);
    return children;
}

const Symbol* Lookup::selectChild(const Symbol& initialSymbol,
                                  std::span<const ElementSelectSyntax* const> selectors,
                                  const ASTContext& context, LookupResult& result) {
    const Symbol* symbol = &initialSymbol;
    const SyntaxNode* prevRangeSelect = nullptr;
    for (const ElementSelectSyntax* syntax : selectors) {
        if (symbol->kind != SymbolKind::InstanceArray &&
            symbol->kind != SymbolKind::GenerateBlockArray) {
            // I think it's safe to assume that the symbol name here will not be empty
            // because if it was, it'd be an instance array or generate array.
            auto& diag = result.addDiag(*context.scope, diag::ScopeNotIndexable,
                                        syntax->sourceRange());
            diag << symbol->name;
            diag.addNote(diag::NoteDeclarationHere, symbol->location);
            return nullptr;
        }

        auto selectorError = [&]() -> const Symbol* {
            result.addDiag(*context.scope, diag::InvalidScopeIndexExpression,
                           syntax->sourceRange());
            return nullptr;
        };

        if (!syntax->selector)
            return selectorError();

        if (prevRangeSelect) {
            result.addDiag(*context.scope, diag::SelectAfterRangeSelect, syntax->sourceRange())
                << prevRangeSelect->sourceRange();
            return nullptr;
        }

        switch (syntax->selector->kind) {
            case SyntaxKind::BitSelect:
                symbol = selectSingleChild(*symbol, syntax->selector->as<BitSelectSyntax>(),
                                           context, result);
                if (!symbol)
                    return nullptr;
                break;
            case SyntaxKind::SimpleRangeSelect:
            case SyntaxKind::AscendingRangeSelect:
            case SyntaxKind::DescendingRangeSelect:
                prevRangeSelect = syntax;
                if (symbol->kind != SymbolKind::InstanceArray)
                    return selectorError();

                symbol = selectChildRange(symbol->as<InstanceArraySymbol>(),
                                          syntax->selector->as<RangeSelectSyntax>(), context,
                                          result);
                if (!symbol)
                    return nullptr;
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }

    return symbol;
}

void Lookup::selectChild(const Type& virtualInterface, SourceRange range,
                         std::span<LookupResult::Selector> selectors, const ASTContext& context,
                         LookupResult& result) {
    NameComponents unused;
    SmallVector<NamePlusLoc, 4> nameParts;
    SmallVector<const ElementSelectSyntax*> elementSelects;
    auto& comp = context.getCompilation();

    for (auto& selector : std::views::reverse(selectors)) {
        if (auto memberSel = std::get_if<LookupResult::MemberSelector>(&selector)) {
            NamePlusLoc npl;
            npl.dotLocation = memberSel->dotLocation;
            npl.name.text = memberSel->name;
            npl.name.range = memberSel->nameRange;
            std::ranges::reverse(elementSelects); // reverse the element selects since we initially
                                                  // saw them in reverse order
            npl.name.selectors = elementSelects.copy(comp);

            nameParts.push_back(npl);
            elementSelects.clear();
        }
        else {
            elementSelects.push_back(std::get<const ElementSelectSyntax*>(selector));
        }
    }

    result.found = getVirtualInterfaceTarget(virtualInterface, context, range);
    lookupDownward(nameParts, unused, context, LookupFlags::None, result);
}

const ClassType* Lookup::findClass(const NameSyntax& className, const ASTContext& context,
                                   std::optional<DiagCode> requireInterfaceClass) {
    LookupResult result;
    Lookup::name(className, context, LookupFlags::Type | LookupFlags::NoSelectors, result);
    result.reportDiags(context);
    if (!result.found)
        return nullptr;

    if (requireInterfaceClass) {
        if (result.flags.has(LookupResultFlags::FromTypeParam)) {
            context.addDiag(diag::IfaceExtendTypeParam, className.sourceRange());
            return nullptr;
        }

        if (result.flags.has(LookupResultFlags::FromForwardTypedef)) {
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

std::pair<const ClassType*, bool> Lookup::getContainingClass(const Scope& scope) {
    auto isClassElem = [](SymbolKind kind) {
        switch (kind) {
            case SymbolKind::StatementBlock:
            case SymbolKind::Subroutine:
            case SymbolKind::MethodPrototype:
            case SymbolKind::ConstraintBlock:
            case SymbolKind::RandSeqProduction:
            case SymbolKind::CovergroupBody:
            case SymbolKind::CovergroupType:
            case SymbolKind::Coverpoint:
            case SymbolKind::CoverCross:
                return true;
            default:
                return false;
        }
    };

    const Symbol* parent = &scope.asSymbol();
    bool inStatic = false;
    while (isClassElem(parent->kind)) {
        if (parent->kind == SymbolKind::Subroutine) {
            // Remember whether this was a static class method.
            if (parent->as<SubroutineSymbol>().flags.has(MethodFlags::Static))
                inStatic = true;
        }
        else if (parent->kind == SymbolKind::MethodPrototype) {
            if (parent->as<MethodPrototypeSymbol>().flags.has(MethodFlags::Static))
                inStatic = true;
        }

        auto parentScope = parent->getParentScope();
        SLANG_ASSERT(parentScope);
        parent = &parentScope->asSymbol();
    }

    if (parent->kind == SymbolKind::ClassType)
        return {&parent->as<ClassType>(), inStatic};

    return {nullptr, inStatic};
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

bool Lookup::isAccessibleFrom(const Symbol& target, const Symbol& sourceScope) {
    auto& parentScope = target.getParentScope()->asSymbol();
    if (&sourceScope == &parentScope)
        return true;

    if (parentScope.kind != SymbolKind::ClassType)
        return false;

    auto& sourceType = sourceScope.as<Type>();
    auto& targetType = parentScope.as<Type>();
    return targetType.isAssignmentCompatible(sourceType);
}

bool Lookup::ensureVisible(const Symbol& symbol, const ASTContext& context,
                           std::optional<SourceRange> sourceRange) {
    LookupResult result;
    if (checkVisibility(symbol, *context.scope, sourceRange, result))
        return true;

    result.reportDiags(context);
    return false;
}

bool Lookup::ensureAccessible(const Symbol& symbol, const ASTContext& context,
                              std::optional<SourceRange> sourceRange) {
    if (context.randomizeDetails && context.randomizeDetails->classType &&
        Lookup::isAccessibleFrom(symbol, context.randomizeDetails->classType->asSymbol())) {
        return true;
    }

    auto [parent, inStatic] = getContainingClass(*context.scope);
    if (parent && !isAccessibleFrom(symbol, *parent) && !withinCovergroup(symbol, *context.scope)) {
        if (sourceRange) {
            auto& diag = context.addDiag(diag::NestedNonStaticClassProperty, *sourceRange);
            diag << symbol.name << parent->name;
        }
        return false;
    }
    else if (inStatic || context.flags.has(ASTFlags::StaticInitializer) ||
             (!parent && !withinCovergroup(symbol, *context.scope))) {
        if (sourceRange)
            context.addDiag(diag::NonStaticClassProperty, *sourceRange) << symbol.name;
        return false;
    }
    return true;
}

bool Lookup::findTempVar(const Scope& scope, const TempVarSymbol& symbol, const NameSyntax& syntax,
                         LookupResult& result) {
    int colonParts = 0;
    SmallVector<NamePlusLoc, 4> nameParts;
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

    const TempVarSymbol* curr = &symbol;
    do {
        if (curr->name == name.text) {
            result.found = curr;
            break;
        }
        curr = curr->nextTemp;
    } while (curr);

    if (!result.found)
        return false;

    ASTContext context(scope, LookupLocation::max);
    return lookupDownward(nameParts, name, context, LookupFlags::None, result);
}

bool Lookup::withinClassRandomize(const ASTContext& context, const NameSyntax& syntax,
                                  bitmask<LookupFlags> flags, LookupResult& result) {
    int colonParts = 0;
    SmallVector<NamePlusLoc, 4> nameParts;
    const NameSyntax* first = &syntax;
    if (syntax.kind == SyntaxKind::ScopedName)
        first = splitScopedName(syntax.as<ScopedNameSyntax>(), nameParts, colonParts);

    SLANG_ASSERT(context.randomizeDetails);
    auto& details = *context.randomizeDetails;
    auto& classScope = *details.classType;

    auto findSuperScope = [&]() -> const Scope& {
        if (details.thisVar) {
            auto dt = details.thisVar->getDeclaredType();
            SLANG_ASSERT(dt);
            return dt->getType().getCanonicalType().as<ClassType>();
        }

        return *context.scope;
    };

    NameComponents name = *first;
    switch (first->kind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            if (name.text.empty())
                return false;

            // If the nameRestrictions list is not empty, we have to verify that the
            // first element is in the list. Otherwise, an empty list indicates that
            // the lookup is unrestricted.
            if (!details.nameRestrictions.empty()) {
                if (std::ranges::find(details.nameRestrictions, name.text) ==
                    details.nameRestrictions.end()) {
                    return false;
                }
            }

            result.found = classScope.find(name.text);
            break;
        case SyntaxKind::ThisHandle:
            result.found = details.thisVar;
            if (!result.found)
                result.found = findThisHandle(*context.scope, flags, name.range, result);

            if (result.found && nameParts.back().kind == SyntaxKind::SuperHandle) {
                // Handle "this.super.whatever" the same as if the user had just
                // written "super.whatever".
                name = nameParts.back().name;
                nameParts.pop_back();
                result.found = findSuperHandle(findSuperScope(), flags, name.range, result);
                colonParts = 1;
            }
            break;
        case SyntaxKind::SuperHandle:
            result.found = findSuperHandle(findSuperScope(), flags, name.range, result);
            colonParts = 1; // pretend we used colon access to resolve class scoped name
            break;
        default:
            // Return not found; the caller should do a normal lookup
            // to handle any of these other cases.
            return false;
    }

    if (!result.found)
        return false;

    ASTContext classContext(classScope, LookupLocation::max);
    if (colonParts) {
        // Disallow package lookups in this function.
        auto isClass = isClassType(*result.found);
        if (!isClass.has_value() || !isClass.value())
            return false;

        if (!resolveColonNames(nameParts, colonParts, name, flags, result, classContext))
            return false;
    }
    else {
        if (!lookupDownward(nameParts, name, classContext, flags, result))
            return false;
    }

    unwrapResult(*context.scope, syntax.sourceRange(), result);
    return true;
}

bool Lookup::findAssertionLocalVar(const ASTContext& context, const NameSyntax& syntax,
                                   LookupResult& result) {
    int colonParts = 0;
    SmallVector<NamePlusLoc, 4> nameParts;
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

    auto inst = context.assertionInstance;
    SLANG_ASSERT(inst);

    while (inst->argDetails)
        inst = inst->argDetails;

    auto& map = inst->localVars;
    auto it = map.find(name.text);
    if (it == map.end())
        return false;

    result.found = it->second;
    return lookupDownward(nameParts, name, context, LookupFlags::None, result);
}

void Lookup::unqualifiedImpl(const Scope& scope, std::string_view name, LookupLocation location,
                             std::optional<SourceRange> sourceRange, bitmask<LookupFlags> flags,
                             SymbolIndex outOfBlockIndex, LookupResult& result,
                             const Scope& originalScope, const SyntaxNode* originalSyntax) {
    auto reportRecursiveError = [&](const Symbol& symbol) {
        if (sourceRange) {
            auto& diag = result.addDiag(scope, diag::RecursiveDefinition, *sourceRange);
            diag << name;
            diag.addNote(diag::NoteDeclarationHere, symbol.location);
        }
        result.found = nullptr;
    };

    // Try a simple name lookup to see if we find anything.
    auto& nameMap = scope.getNameMap();
    const Symbol* symbol = nullptr;
    if (auto it = nameMap.find(name); it != nameMap.end()) {
        // If the lookup is for a local name, check that we can access the symbol (it must be
        // declared before use). Callables and block names can be referenced anywhere in the
        // scope, so the location doesn't matter for them.
        symbol = it->second;
        bool locationGood = LookupLocation::before(*symbol) < location;
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
                case SymbolKind::Subroutine: {
                    // Subroutines can be referenced before they are declared if they
                    // are tasks or return void (tasks are always set to have a void
                    // return type internally so we only need one check here).
                    //
                    // It's important to check that we're not in the middle of evaluating
                    // the return type before we try to access that return type or
                    // we'll hard fail.
                    auto& sub = symbol->as<SubroutineSymbol>();
                    if (sub.declaredReturnType.isEvaluating()) {
                        reportRecursiveError(*symbol);
                        return;
                    }

                    // Also allow built-ins to always be found; they don't really
                    // have a location since they're intrinsically defined.
                    locationGood = sub.getReturnType().isVoid() ||
                                   sub.flags.has(MethodFlags::BuiltIn);
                    break;
                }
                case SymbolKind::MethodPrototype: {
                    // Same as above.
                    auto& sub = symbol->as<MethodPrototypeSymbol>();
                    if (sub.declaredReturnType.isEvaluating()) {
                        reportRecursiveError(*symbol);
                        return;
                    }

                    locationGood = sub.getReturnType().isVoid() ||
                                   sub.flags.has(MethodFlags::BuiltIn);
                    break;
                }
                case SymbolKind::Sequence:
                case SymbolKind::Property:
                    // Sequences and properties can always be referenced before declaration.
                    locationGood = true;
                    break;
                case SymbolKind::Parameter:
                case SymbolKind::Specparam:
                case SymbolKind::EnumValue:
                    // Constants can never be looked up before their declaration,
                    // to avoid problems with recursive constant evaluation.
                    flags &= ~LookupFlags::AllowDeclaredAfter;
                    break;
                default:
                    break;
            }

            if (forward) {
                locationGood = LookupLocation::before(*forward) < location;
                result.flags |= LookupResultFlags::FromForwardTypedef;
            }
        }
        else if (symbol->kind == SymbolKind::TransparentMember && originalSyntax) {
            // Enum values are special in that we can't always get a precise ordering
            // of where they are declared in a scope, since they can be declared inside
            // a nested subexpression. Check for correct location by looking at the
            // actual source locations involved.
            auto& wrapped = symbol->as<TransparentMemberSymbol>().wrapped;
            if (wrapped.kind == SymbolKind::EnumValue) {
                // If the enum was inherited from a base class then we shouldn't
                // worry about the source location; the base class may be declared
                // later in the file.
                bool skipLocationCheck = false;
                auto enumScope = wrapped.getParentScope()->asSymbol().getParentScope();
                SLANG_ASSERT(enumScope);
                if (enumScope->asSymbol().kind == SymbolKind::ClassType) {
                    auto containingClass = getContainingClass(scope).first;
                    if (containingClass &&
                        containingClass->isDerivedFrom(enumScope->asSymbol().as<ClassType>())) {
                        skipLocationCheck = true;
                    }
                }

                if (auto sm = scope.getCompilation().getSourceManager(); sm && !skipLocationCheck) {
                    auto loc = originalSyntax->getFirstToken().location();
                    locationGood =
                        sm->isBeforeInCompilationUnit(wrapped.location, loc).value_or(true);
                }
            }
        }

        if (locationGood || flags.has(LookupFlags::AllowDeclaredAfter)) {
            // Unwrap the symbol if it's hidden behind an import or hoisted enum member.
            if (symbol->kind == SymbolKind::TransparentMember) {
                do {
                    symbol = &symbol->as<TransparentMemberSymbol>().wrapped;
                } while (symbol->kind == SymbolKind::TransparentMember);

                // Special case check for a lookup finding hoisted members of an anonymous
                // program. For these we need to verify that the original lookup location is
                // also in a program.
                if (symbol->getParentScope()->asSymbol().kind == SymbolKind::AnonymousProgram &&
                    !isInProgram(originalScope.asSymbol()) && sourceRange) {
                    auto& diag = result.addDiag(scope, diag::IllegalReferenceToProgramItem,
                                                *sourceRange);
                    diag.addNote(diag::NoteDeclarationHere, symbol->location);
                }
            }

            switch (symbol->kind) {
                case SymbolKind::ExplicitImport:
                    result.found = symbol->as<ExplicitImportSymbol>().importedSymbol();
                    result.flags |= LookupResultFlags::WasImported;
                    scope.getCompilation().noteReference(*symbol);
                    break;
                case SymbolKind::ForwardingTypedef:
                    // If we find a forwarding typedef, the actual typedef was never defined.
                    // Just ignore it, we'll issue a better error later.
                    break;
                case SymbolKind::MethodPrototype:
                    // Looking up a prototype should always forward on to the actual method.
                    result.found = symbol->as<MethodPrototypeSymbol>().getSubroutine();
                    break;
                case SymbolKind::ModportClocking:
                    result.found = symbol->as<ModportClockingSymbol>().target;
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
            bool done = true;
            if (result.found) {
                auto declaredType = result.found->getDeclaredType();
                if (declaredType && declaredType->isEvaluating()) {
                    if (locationGood) {
                        reportRecursiveError(*result.found);
                    }
                    else {
                        // We overrode the location checking via a flag and
                        // it's probably biting us now by causing us to find
                        // our own symbol when we otherwise shouldn't.
                        // Work around this by just pretending we didn't find anything.
                        done = false;
                        result.clear();
                    }
                }
            }

            if (done)
                return;
        }
    }

    // Look through any wildcard imports prior to the lookup point and see if their packages
    // contain the name we're looking for.
    if (auto wildcardImportData = scope.getWildcardImportData()) {
        if (flags.has(LookupFlags::DisallowWildcardImport)) {
            // We're in a context that disallows new imports via wildcard imports,
            // but we can still reference any symbols that were previously imported
            // that way from some other lookup. In order to be sure we've seen all of
            // those lookups we need to force elaborate the scope first.
            if (!wildcardImportData->hasForceElaborated) {
                wildcardImportData->hasForceElaborated = true;
                scope.getCompilation().forceElaborate(scope.asSymbol());
            }

            if (auto it = wildcardImportData->importedSymbols.find(name);
                it != wildcardImportData->importedSymbols.end()) {
                result.flags |= LookupResultFlags::WasImported;
                result.found = it->second;
                return;
            }
        }
        else {
            struct Import {
                const Symbol* imported;
                const WildcardImportSymbol* import;
            };
            SmallVector<Import, 4> imports;
            SmallSet<const Symbol*, 2> importDedup;

            for (auto import : wildcardImportData->wildcardImports) {
                if (location < LookupLocation::after(*import))
                    break;

                auto package = import->getPackage();
                if (!package) {
                    result.flags |= LookupResultFlags::SuppressUndeclared;
                    continue;
                }

                const Symbol* imported = package->findForImport(name);
                if (imported && importDedup.emplace(imported).second)
                    imports.emplace_back(Import{imported, import});
            }

            if (!imports.empty()) {
                if (imports.size() > 1) {
                    if (sourceRange) {
                        auto& diag = result.addDiag(scope, diag::AmbiguousWildcardImport,
                                                    *sourceRange);
                        diag << name;
                        for (const auto& pair : imports) {
                            diag.addNote(diag::NoteImportedFrom, pair.import->location);
                            diag.addNote(diag::NoteDeclarationHere, pair.imported->location);
                        }
                    }
                    return;
                }

                if (symbol && sourceRange) {
                    // The existing symbol might be an import for the thing we just imported
                    // via wildcard, which is fine so don't error for that case.
                    if (symbol->kind != SymbolKind::ExplicitImport ||
                        symbol->as<ExplicitImportSymbol>().importedSymbol() !=
                            imports[0].imported) {

                        auto& diag = result.addDiag(scope, diag::ImportNameCollision, *sourceRange);
                        diag << name;
                        diag.addNote(diag::NoteDeclarationHere, symbol->location);
                        diag.addNote(diag::NoteImportedFrom, imports[0].import->location);
                        diag.addNote(diag::NoteDeclarationHere, imports[0].imported->location);
                    }
                }

                result.flags |= LookupResultFlags::WasImported;
                result.found = imports[0].imported;
                scope.getCompilation().noteReference(*imports[0].import);

                wildcardImportData->importedSymbols.try_emplace(result.found->name, result.found);
                return;
            }
        }
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
    auto& sym = scope.asSymbol();
    if (sym.kind == SymbolKind::Subroutine) {
        outOfBlockIndex = sym.as<SubroutineSymbol>().outOfBlockIndex;
    }
    else if (sym.kind == SymbolKind::ConstraintBlock) {
        outOfBlockIndex = sym.as<ConstraintBlockSymbol>().getOutOfBlockIndex();
    }
    else if (uint32_t(outOfBlockIndex) != 0) {
        location = LookupLocation(location.getScope(), uint32_t(outOfBlockIndex));
        outOfBlockIndex = SymbolIndex(0);
    }

    if (sym.kind == SymbolKind::ClassType) {
        // Suppress errors when we fail to find a symbol inside a class that
        // had a problem resolving its base class, since the symbol may be
        // expected to be defined in the base.
        auto baseClass = sym.as<ClassType>().getBaseClass();
        if (baseClass && baseClass->isError())
            result.flags |= LookupResultFlags::SuppressUndeclared;
    }

    if (flags.has(LookupFlags::DisallowUnitReferences) &&
        location.getScope()->asSymbol().kind == SymbolKind::CompilationUnit) {
        return;
    }

    return unqualifiedImpl(*location.getScope(), name, location, sourceRange, flags,
                           outOfBlockIndex, result, originalScope, originalSyntax);
}

void Lookup::qualified(const ScopedNameSyntax& syntax, const ASTContext& context,
                       bitmask<LookupFlags> flags, LookupResult& result) {
    // Split the name into easier to manage chunks. The parser will always produce a
    // left-recursive name tree, so that's all we'll bother to handle.
    int colonParts = 0;
    SmallVector<NamePlusLoc, 4> nameParts;
    auto leftMost = splitScopedName(syntax, nameParts, colonParts);

    SyntaxKind firstKind = leftMost->kind;
    NameComponents first = *leftMost;
    auto name = first.text;

    auto popFront = [&] {
        first = nameParts.back().name;
        firstKind = nameParts.back().kind;
        nameParts.pop_back();
        name = first.text;
        if (colonParts)
            colonParts--;
    };

    auto& scope = *context.scope;
    auto& compilation = context.getCompilation();

    if (firstKind == SyntaxKind::LocalScope) {
        if (!context.randomizeDetails || !context.randomizeDetails->classType) {
            result.addDiag(scope, diag::LocalNotAllowed, first.range);
            return;
        }

        // The local:: is allowed here. Pop it and look up the rest of
        // the name as if the local hadn't been specified -- the local
        // lookup portion has already been ensured because we exited
        // early from withinClassRandomize.
        popFront();
    }

    if (name.empty())
        return;

    switch (firstKind) {
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ClassName:
            // Start by trying to find the first name segment using normal unqualified lookup
            unqualifiedImpl(scope, name, context.getLocation(), first.range, flags, {}, result,
                            scope, nullptr);
            break;
        case SyntaxKind::UnitScope: {
            // Walk upward to find the compilation unit scope.
            popFront();
            if (name.empty())
                return;

            const Scope* current = &scope;
            LookupLocation location = context.getLocation();
            do {
                auto& symbol = current->asSymbol();
                if (symbol.kind == SymbolKind::CompilationUnit) {
                    unqualifiedImpl(*current, name, location, first.range, flags, {}, result, scope,
                                    nullptr);
                    break;
                }

                location = LookupLocation::after(symbol);
                current = location.getScope();
            } while (current);

            break;
        }
        case SyntaxKind::RootScope:
            // Ignore hierarchical lookups that occur inside uninstantiated modules.
            if (scope.isUninstantiated())
                return;

            result.found = &compilation.getRoot();
            lookupDownward(nameParts, first, context, flags, result);
            return;
        case SyntaxKind::ThisHandle:
            result.found = findThisHandle(scope, flags, first.range, result);
            if (result.found && nameParts.back().kind == SyntaxKind::SuperHandle) {
                // Handle "this.super.whatever" the same as if the user had just
                // written "super.whatever".
                first = nameParts.back().name;
                nameParts.pop_back();
                result.found = findSuperHandle(scope, flags, first.range, result);
                colonParts = 1;
            }
            break;
        case SyntaxKind::SuperHandle:
            result.found = findSuperHandle(scope, flags, first.range, result);
            colonParts = 1; // pretend we used colon access to resolve class scoped name
            break;
        case SyntaxKind::LocalScope:
            // This is only reachable in invalid code. An error has already been
            // reported so early out.
            return;
        case SyntaxKind::ArrayUniqueMethod:
        case SyntaxKind::ArrayAndMethod:
        case SyntaxKind::ArrayOrMethod:
        case SyntaxKind::ArrayXorMethod:
        case SyntaxKind::ConstructorName:
            result.addDiag(scope, diag::UnexpectedNameToken, first.range) << name;
            return;
        default:
            SLANG_UNREACHABLE;
    }

    if (result.hasError())
        return;

    // [23.7.1] If we are starting with a colon separator, always do a downwards name
    // resolution.
    if (colonParts) {
        resolveColonNames(nameParts, colonParts, first, flags, result, context);
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
        if (!lookupDownward(nameParts, first, context, flags, result))
            return;

        // If we found a symbol, we're done with lookup. In case (1) above we'll always have a
        // found symbol here. Otherwise, if we're in case (2) we need to do further upwards name
        // lookup. If we're in case (3) we've already issued an error and just need to give up.
        if (result.found || result.flags.has(LookupResultFlags::WasImported))
            return;

        originalResult = result;
    }

    // If we reach this point we're in case (2) or (4) above. Go up through the instantiation
    // hierarchy and see if we can find a match there.
    if (!lookupUpward(nameParts, first, context, flags, result))
        return;

    if (result.found)
        return;

    // We couldn't find anything. originalResult has any diagnostics issued by the first
    // downward lookup (if any), so it's fine to just return it as is. If we never found any
    // symbol originally, issue an appropriate error for that.
    result = originalResult;
    if (!result.found && !result.hasError()) {
        reportUndeclared(scope, name, first.range,
                         flags | LookupFlags::NoUndeclaredErrorIfUninstantiated, true, result);
    }
}

void Lookup::reportUndeclared(const Scope& initialScope, std::string_view name, SourceRange range,
                              bitmask<LookupFlags> flags, bool isHierarchical,
                              LookupResult& result) {
    // If the caller doesn't want an error, don't give him one.
    if (flags.has(LookupFlags::NoUndeclaredError) ||
        (flags.has(LookupFlags::NoUndeclaredErrorIfUninstantiated) &&
         initialScope.isUninstantiated())) {
        return;
    }

    // If we observed a wildcard import we couldn't resolve, we shouldn't report an
    // error for an undeclared identifier because maybe it's supposed to come from that package.
    // In particular it's important that we do this because when we first look at a
    // definition because it's possible we haven't seen the file containing the package yet.
    // This also gets set for class scopes that have an error base class.
    if (result.flags.has(LookupResultFlags::SuppressUndeclared))
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
    while (true) {
        // This lambda returns true if the given symbol is a viable candidate
        // for the kind of lookup that was being performed.
        auto isViable = [flags, &initialScope](const Symbol& sym) {
            const Symbol* s = &sym;
            if (s->kind == SymbolKind::TransparentMember)
                s = &s->as<TransparentMemberSymbol>().wrapped;

            if (flags.has(LookupFlags::Type)) {
                if (!s->isType() && s->kind != SymbolKind::TypeParameter &&
                    s->kind != SymbolKind::GenericClassDef) {
                    return false;
                }
            }
            else {
                switch (s->kind) {
                    case SymbolKind::Subroutine:
                    case SymbolKind::InstanceArray:
                    case SymbolKind::Sequence:
                    case SymbolKind::Property:
                    case SymbolKind::Checker:
                    case SymbolKind::UninstantiatedDef:
                        break;
                    case SymbolKind::Instance:
                        if (!s->as<InstanceSymbol>().isInterface())
                            return false;
                        break;
                    default:
                        if (!s->isValue())
                            return false;
                        break;
                }
            }

            // Ignore special members.
            if (s->kind == SymbolKind::Subroutine &&
                s->as<SubroutineSymbol>().flags.has(MethodFlags::Constructor)) {
                return false;
            }

            if (VariableSymbol::isKind(s->kind) &&
                s->as<VariableSymbol>().flags.has(VariableFlags::CompilerGenerated)) {
                return false;
            }

            if (!isVisibleFrom(*s, initialScope))
                return false;

            return true;
        };

        if (!flags.has(LookupFlags::AllowDeclaredAfter)) {
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

                    int dist = editDistance(member.name, name, /* allowReplacements */ true,
                                            bestDistance);
                    if (dist < bestDistance) {
                        closestSym = &member;
                        bestDistance = dist;
                    }
                }
            };

            // Check the current scope.
            checkMembers(*scope);

            // Also search in package imports.
            if (auto importData = scope->getWildcardImportData()) {
                for (auto import : importData->wildcardImports) {
                    auto package = import->getPackage();
                    if (package)
                        checkMembers(*package);
                }
            }
        }

        scope = scope->asSymbol().getParentScope();
        if (!scope || (scope->asSymbol().kind == SymbolKind::CompilationUnit &&
                       flags.has(LookupFlags::DisallowUnitReferences))) {
            break;
        }
    }

    // If we found the actual named symbol and it's viable for our kind of lookup,
    // report a diagnostic about it being used before declared.
    if (usedBeforeDeclared) {
        auto& diag = result.addDiag(initialScope, diag::UsedBeforeDeclared, range);
        diag << name;
        diag.addNote(diag::NoteDeclarationHere, actualSym->location);
        return;
    }

    // Otherwise, check if this names a definition, in which case we can give a nicer error.
    if (auto def = comp.tryGetDefinition(name, initialScope).definition;
        def && def->kind == SymbolKind::Definition) {
        if (isHierarchical) {
            result.addDiag(initialScope, diag::CouldNotResolveHierarchicalPath, range) << name;
        }
        else {
            auto code = flags.has(LookupFlags::Type) ? diag::DefinitionUsedAsType
                                                     : diag::DefinitionUsedAsValue;
            result.addDiag(initialScope, code, range)
                << name << def->as<DefinitionSymbol>().getArticleKindString();
        }
        return;
    }

    // Also check for a package with this name.
    if (comp.getPackage(name)) {
        result.addDiag(initialScope, diag::UndeclaredButFoundPackage, range.end()) << name << range;
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

    // We couldn't make any sense of this, just report a simple error about a missing identifier.
    result.addDiag(initialScope, diag::UndeclaredIdentifier, range) << name;
}

} // namespace slang::ast

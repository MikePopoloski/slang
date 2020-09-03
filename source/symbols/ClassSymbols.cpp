//------------------------------------------------------------------------------
// ClassSymbols.cpp
// Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/ClassSymbols.h"

#include "ParameterBuilder.h"

#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AllTypes.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

ClassPropertySymbol::ClassPropertySymbol(string_view name, SourceLocation loc,
                                         VariableLifetime lifetime, Visibility visibility,
                                         uint32_t index) :
    VariableSymbol(SymbolKind::ClassProperty, name, loc, lifetime),
    visibility(visibility), index(index) {
}

void ClassPropertySymbol::fromSyntax(const Scope& scope,
                                     const ClassPropertyDeclarationSyntax& syntax,
                                     SmallVector<const ClassPropertySymbol*>& results) {
    auto& comp = scope.getCompilation();
    auto& dataSyntax = syntax.declaration->as<DataDeclarationSyntax>();

    bool isConst = false;
    VariableLifetime lifetime = VariableLifetime::Automatic;
    Visibility visibility = Visibility::Public;

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                lifetime = VariableLifetime::Static;
                break;
            case TokenKind::LocalKeyword:
                visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                visibility = Visibility::Protected;
                break;
            case TokenKind::RandKeyword:
            case TokenKind::RandCKeyword:
                scope.addDiag(diag::NotYetSupported, qual.range());
                break;
            case TokenKind::PureKeyword:
            case TokenKind::VirtualKeyword:
            case TokenKind::ExternKeyword:
                // These are not allowed on properties; the parser will issue a diagnostic
                // so just ignore them here.
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    for (Token mod : dataSyntax.modifiers) {
        switch (mod.kind) {
            case TokenKind::VarKeyword:
            case TokenKind::AutomaticKeyword:
                break;
            case TokenKind::ConstKeyword:
                isConst = true;
                break;
            case TokenKind::StaticKeyword:
                lifetime = VariableLifetime::Static;
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    // TODO: set correct index of property among all other properties
    uint32_t index = 0;

    for (auto declarator : dataSyntax.declarators) {
        auto var = comp.emplace<ClassPropertySymbol>(
            declarator->name.valueText(), declarator->name.location(), lifetime, visibility, index);
        var->isConstant = isConst;
        var->setDeclaredType(*dataSyntax.type);
        var->setFromDeclarator(*declarator);
        var->setAttributes(scope, syntax.attributes);
        results.append(var);
    }
}

void ClassType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void ClassType::checkForwardDecls() const {
    if (firstForward)
        firstForward->checkType(ForwardingTypedefSymbol::Class, Visibility::Public, location);
}

void ClassPropertySymbol::serializeTo(ASTSerializer& serializer) const {
    VariableSymbol::serializeTo(serializer);
    serializer.write("visibility", toString(visibility));
}

ClassType::ClassType(Compilation& compilation, string_view name, SourceLocation loc) :
    Type(SymbolKind::ClassType, name, loc), Scope(compilation, this) {
}

ConstantValue ClassType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

const Symbol& ClassType::fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    // If this class declaration has parameter ports it's actually a generic class definition.
    // Create that now and wait until someone specializes it in order to get an actual type.
    if (syntax.parameters && !syntax.parameters->declarations.empty())
        return GenericClassDefSymbol::fromSyntax(scope, syntax);

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ClassType>(comp, syntax.name.valueText(), syntax.name.location());
    return result->populate(scope, syntax);
}

const Type& ClassType::populate(const Scope& scope, const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    if (syntax.virtualOrInterface) {
        // TODO: support this
        scope.addDiag(diag::NotYetSupported, syntax.virtualOrInterface.range());
        return comp.getErrorType();
    }

    setSyntax(syntax);
    for (auto member : syntax.items)
        addMembers(*member);

    // TODO: extends
    // TODO: implements
    // TODO: lifetime

    return *this;
}

void ClassType::serializeTo(ASTSerializer& serializer) const {
    if (firstForward)
        serializer.write("forward", *firstForward);
}

const Symbol& GenericClassDefSymbol::fromSyntax(const Scope& scope,
                                                const ClassDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.allocGenericClass(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);

    // Extract information about parameters and save it for later use
    // when building specializations.
    ASSERT(syntax.parameters);
    ParameterBuilder::createDecls(scope, *syntax.parameters, result->paramDecls);

    return *result;
}

const Type* GenericClassDefSymbol::getDefaultSpecialization(Compilation& compilation) const {
    if (defaultSpecialization)
        return *defaultSpecialization;

    auto result = getSpecializationImpl(compilation, LookupLocation::max, location, nullptr);
    defaultSpecialization = result;
    return result;
}

const Type& GenericClassDefSymbol::getSpecialization(
    Compilation& compilation, LookupLocation lookupLocation,
    const ParameterValueAssignmentSyntax& syntax) const {

    auto result = getSpecializationImpl(compilation, lookupLocation,
                                        syntax.getFirstToken().location(), &syntax);
    if (!result)
        return compilation.getErrorType();

    return *result;
}

const Type* GenericClassDefSymbol::getSpecializationImpl(
    Compilation& compilation, LookupLocation lookupLocation, SourceLocation instanceLoc,
    const ParameterValueAssignmentSyntax* syntax) const {

    auto scope = getParentScope();
    ASSERT(scope);

    // Create a class type instance to hold the parameters. If it turns out we already
    // have this specialization cached we'll throw it away, but that's not a big deal.
    auto classType = compilation.emplace<ClassType>(compilation, name, location);

    ParameterBuilder paramBuilder(*scope, name, paramDecls);
    if (syntax)
        paramBuilder.setAssignments(*syntax);

    // If this is for the default specialization, `syntax` will be null.
    // We want to suppress errors about params not having values and just
    // return null so that the caller can figure out if this is actually a problem.
    bool isForDefault = syntax == nullptr;
    if (!paramBuilder.createParams(*classType, lookupLocation, instanceLoc,
                                   /* forceInvalidValues */ false, isForDefault)) {
        if (isForDefault)
            return nullptr;

        // Otherwise use an error type instead.
        return &compilation.getErrorType();
    }

    SpecializationKey key(*this, paramBuilder.paramValues.copy(compilation),
                          paramBuilder.typeParams.copy(compilation));
    if (auto it = specializations.find(key); it != specializations.end())
        return it->second;

    // Not found, so this is a new entry. Fill in its members and store the
    // specialization for later lookup.
    const Type& result = classType->populate(*scope, getSyntax()->as<ClassDeclarationSyntax>());
    specializations.emplace(key, &result);
    return &result;
}

void GenericClassDefSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

GenericClassDefSymbol::SpecializationKey::SpecializationKey(
    const GenericClassDefSymbol& def, span<const ConstantValue* const> paramValues,
    span<const Type* const> typeParams) :
    definition(&def),
    paramValues(paramValues), typeParams(typeParams) {

    // Precompute the hash.
    size_t h = 0;
    hash_combine(h, definition);
    for (auto val : paramValues)
        hash_combine(h, val ? val->hash() : 0);
    for (auto type : typeParams)
        hash_combine(h, type ? type->hash() : 0);
    savedHash = h;
}

bool GenericClassDefSymbol::SpecializationKey::operator==(const SpecializationKey& other) const {
    if (savedHash != other.savedHash || definition != other.definition ||
        paramValues.size() != other.paramValues.size() ||
        typeParams.size() != other.typeParams.size()) {
        return false;
    }

    for (auto lit = paramValues.begin(), rit = other.paramValues.begin(); lit != paramValues.end();
         lit++, rit++) {
        const ConstantValue* l = *lit;
        const ConstantValue* r = *rit;
        if (l && r) {
            if (!(*l == *r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    for (auto lit = typeParams.begin(), rit = other.typeParams.begin(); lit != typeParams.end();
         lit++, rit++) {
        const Type* l = *lit;
        const Type* r = *rit;
        if (l && r) {
            if (!l->isMatching(*r))
                return false;
        }
        else {
            if (l != r)
                return false;
        }
    }

    return true;
}

} // namespace slang

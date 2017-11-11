//------------------------------------------------------------------------------
// SymbolFactory.cpp
// Symbol creation and caching.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "SymbolFactory.h"

namespace slang {

SymbolFactory::SymbolFactory() :
    shortIntType(TokenKind::ShortIntKeyword, 16, true, false),
    intType(TokenKind::IntKeyword, 32, true, false),
    longIntType(TokenKind::LongIntKeyword, 164, true, false),
    byteType(TokenKind::ByteKeyword, 8, true, false),
    bitType(TokenKind::BitKeyword, 1, false, false),
    logicType(TokenKind::LogicKeyword, 1, false, true),
    regType(TokenKind::RegKeyword, 1, false, true),
    integerType(TokenKind::IntegerKeyword, 32, true, true),
    timeType(TokenKind::TimeKeyword, 64, false, true),
    realType(TokenKind::RealKeyword, 64),
    realTimeType(TokenKind::RealTimeKeyword, 64),
    shortRealType(TokenKind::ShortRealKeyword, 64),
    stringType(SymbolKind::StringType, "string"),
    chandleType(SymbolKind::CHandleType, "chandle"),
    voidType(SymbolKind::VoidType, "void"),
    eventType(SymbolKind::EventType, "event")
{
    // Register built-in types for lookup by syntax kind.
    knownTypes[SyntaxKind::ShortIntType] = &shortIntType;
    knownTypes[SyntaxKind::IntType] = &intType;
    knownTypes[SyntaxKind::LongIntType] = &longIntType;
    knownTypes[SyntaxKind::ByteType] = &byteType;
    knownTypes[SyntaxKind::BitType] = &bitType;
    knownTypes[SyntaxKind::LogicType] = &logicType;
    knownTypes[SyntaxKind::RegType] = &regType;
    knownTypes[SyntaxKind::IntegerType] = &integerType;
    knownTypes[SyntaxKind::TimeType] = &timeType;
    knownTypes[SyntaxKind::RealType] = &realType;
    knownTypes[SyntaxKind::RealTimeType] = &realTimeType;
    knownTypes[SyntaxKind::ShortRealType] = &shortRealType;
    knownTypes[SyntaxKind::StringType] = &stringType;
    knownTypes[SyntaxKind::CHandleType] = &chandleType;
    knownTypes[SyntaxKind::VoidType] = &voidType;
    knownTypes[SyntaxKind::EventType] = &eventType;
    knownTypes[SyntaxKind::Unknown] = &errorType;
}

const CompilationUnitSymbol& SymbolFactory::createCompilationUnit(const SyntaxNode& node, const ScopeSymbol& parent) {
    SmallVectorSized<const Symbol*, 4> symbols;
    createSymbols(node, parent, symbols);

    if (node.kind == SyntaxKind::CompilationUnit) {
        ASSERT(symbols.size() == 1);
        return symbols[0]->as<CompilationUnitSymbol>();
    }
    else {
        auto unit = alloc.emplace<CompilationUnitSymbol>(parent);
        unit->setMembers(symbols);
        return *unit;
    }
}

void SymbolFactory::createSymbols(const SyntaxNode& node, const ScopeSymbol& parent,
                                  SmallVector<const Symbol*>& symbols) {
    switch (node.kind) {
        case SyntaxKind::CompilationUnit: {
            auto unit = alloc.emplace<CompilationUnitSymbol>(parent);
            createChildren(unit, node.as<CompilationUnitSyntax>());
            symbols.append(unit);
            break;
        }
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ProgramDeclaration:
            symbols.append(alloc.emplace<DefinitionSymbol>(node.as<ModuleDeclarationSyntax>(), parent));
            break;
        case SyntaxKind::PackageDeclaration: {
            string_view name = node.as<ModuleDeclarationSyntax>().header.name.valueText();
            auto symbol = alloc.emplace<PackageSymbol>(name, parent);
            createChildren(symbol, node.as<ModuleDeclarationSyntax>());
            symbols.append(symbol);
            break;
        }
        case SyntaxKind::PackageImportDeclaration:
            for (auto item : node.as<PackageImportDeclarationSyntax>().items) {
                if (item->item.kind == TokenKind::Star) {
                    symbols.append(alloc.emplace<WildcardImportSymbol>(
                        item->package.valueText(),
                        item->item.location(),
                        parent));
                }
                else {
                    symbols.append(alloc.emplace<ExplicitImportSymbol>(
                        item->package.valueText(),
                        item->item.valueText(),
                        item->item.location(),
                        parent));
                }
            }
            break;
        case SyntaxKind::HierarchyInstantiation:
            InstanceSymbol::fromSyntax(parent, node.as<HierarchyInstantiationSyntax>(), symbols);
            break;
        case SyntaxKind::IfGenerate:
            // TODO: add special name conflict checks for generate blocks
            symbols.append(alloc.emplace<IfGenerateSymbol>(node.as<IfGenerateSyntax>(), parent));
            break;
        case SyntaxKind::LoopGenerate:
            symbols.append(alloc.emplace<LoopGenerateSymbol>(node.as<LoopGenerateSyntax>(), parent));
            break;
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
            symbols.append(alloc.emplace<SubroutineSymbol>(node.as<FunctionDeclarationSyntax>(), parent));
            break;
        case SyntaxKind::DataDeclaration: {
            SmallVectorSized<const VariableSymbol*, 4> variables;
            VariableSymbol::fromSyntax(parent, node.as<DataDeclarationSyntax>(), variables);

            for (auto variable : variables)
                symbols.append(variable);
            break;
        }
        case SyntaxKind::ParameterDeclarationStatement: {
            const ParameterDeclarationSyntax& declaration = node.as<ParameterDeclarationStatementSyntax>().parameter;
            for (const VariableDeclaratorSyntax* decl : declaration.declarators) {

                // TODO: hack to get param values working
                //auto it = paramAssignments.find(decl->name.valueText());
                const ConstantValue& cv = parent.evaluateConstant(decl->initializer->expr);

                symbols.append(alloc.emplace<ParameterSymbol>(decl->name.valueText(), decl->name.location(),
                                                              getIntType(), cv, parent));
            }
            break;
        }
        case SyntaxKind::AlwaysBlock:
        case SyntaxKind::AlwaysCombBlock:
        case SyntaxKind::AlwaysLatchBlock:
        case SyntaxKind::AlwaysFFBlock:
        case SyntaxKind::InitialBlock:
        case SyntaxKind::FinalBlock: {
            auto kind = SemanticFacts::getProceduralBlockKind(node.as<ProceduralBlockSyntax>().kind);
            symbols.append(alloc.emplace<ProceduralBlockSymbol>(parent, kind));
            break;
        }
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            symbols.append(&IntegralTypeSymbol::fromSyntax(*this, node.as<IntegerTypeSyntax>(), parent));
            break;
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            // TODO: signing
            // TODO: report this error in the parser?
            //auto& its = syntax.as<IntegerTypeSyntax>();
            //if (its.dimensions.count() > 0) {
            //    // Error but don't fail out; just remove the dims and keep trucking
            //    auto& diag = addError(DiagCode::PackedDimsOnPredefinedType, its.dimensions[0]->openBracket.location());
            //    diag << getTokenKindText(its.keyword.kind);
            //}
            symbols.append(&getType(node.kind));
            break;
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
            symbols.append(&getType(node.kind));
            break;
        default:
            THROW_UNREACHABLE;
    }
}

static TokenKind getIntegralKeywordKind(bool isFourState, bool isReg) {
    return !isFourState ? TokenKind::BitKeyword : isReg ? TokenKind::RegKeyword : TokenKind::LogicKeyword;
}

const TypeSymbol& SymbolFactory::getType(SyntaxKind typeKind) const {
    auto it = knownTypes.find(typeKind);
    return it == knownTypes.end() ? errorType : *it->second;
}

const TypeSymbol& SymbolFactory::getType(const DataTypeSyntax& node, const ScopeSymbol& parent) {
    SmallVectorSized<const Symbol*, 2> results;
    createSymbols(node, parent, results);
    ASSERT(results.size() == 1);
    return results[0]->as<TypeSymbol>();
}

const IntegralTypeSymbol& SymbolFactory::getType(int width, bool isSigned, bool isFourState, bool isReg) {
    uint64_t key = width;
    key |= uint64_t(isSigned) << 32;
    key |= uint64_t(isFourState) << 33;
    key |= uint64_t(isReg) << 34;

    auto it = integralTypeCache.find(key);
    if (it != integralTypeCache.end())
        return *it->second;

    TokenKind type = getIntegralKeywordKind(isFourState, isReg);
    auto symbol = alloc.emplace<IntegralTypeSymbol>(type, width, isSigned, isFourState);
    integralTypeCache.emplace_hint(it, key, symbol);
    return *symbol;
}

const IntegralTypeSymbol& SymbolFactory::getType(int width, bool isSigned, bool isFourState, bool isReg,
                                                 span<const int> lowerBounds, span<const int> widths) {
    TokenKind type = getIntegralKeywordKind(isFourState, isReg);
    return *alloc.emplace<IntegralTypeSymbol>(type, width, isSigned, isFourState, lowerBounds, widths);
}

template<typename TNode>
void SymbolFactory::createChildren(ScopeSymbol* scope, const TNode& node) {
    SmallVectorSized<const Symbol*, 16> symbols;
    for (auto member : node.members)
        createSymbols(*member, *scope, symbols);
    scope->setMembers(symbols);
}

}
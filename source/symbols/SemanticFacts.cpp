//------------------------------------------------------------------------------
// SemanticFacts.cpp
// Semantic enums and conversion methods
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/SemanticFacts.h"

#include "slang/syntax/AllSyntax.h"

namespace slang {

// clang-format off
std::optional<VariableLifetime> SemanticFacts::getVariableLifetime(Token token) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        case TokenKind::Unknown: return std::nullopt;
        default: THROW_UNREACHABLE;
    }
}

PortDirection SemanticFacts::getPortDirection(TokenKind kind) {
    switch (kind) {
        case TokenKind::InputKeyword: return PortDirection::In;
        case TokenKind::InOutKeyword: return PortDirection::InOut;
        case TokenKind::OutputKeyword: return PortDirection::Out;
        case TokenKind::RefKeyword: return PortDirection::Ref;
        default: THROW_UNREACHABLE;
    }
}

ProceduralBlockKind SemanticFacts::getProceduralBlockKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AlwaysBlock: return ProceduralBlockKind::Always;
        case SyntaxKind::AlwaysCombBlock: return ProceduralBlockKind::AlwaysComb;
        case SyntaxKind::AlwaysLatchBlock: return ProceduralBlockKind::AlwaysLatch;
        case SyntaxKind::AlwaysFFBlock: return ProceduralBlockKind::AlwaysFF;
        case SyntaxKind::InitialBlock: return ProceduralBlockKind::Initial;
        case SyntaxKind::FinalBlock: return ProceduralBlockKind::Final;
        default: THROW_UNREACHABLE;
    }
}

DefinitionKind SemanticFacts::getDefinitionKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::ModuleDeclaration: return DefinitionKind::Module;
        case SyntaxKind::InterfaceDeclaration: return DefinitionKind::Interface;
        case SyntaxKind::ProgramDeclaration: return DefinitionKind::Program;
        default: THROW_UNREACHABLE;
    }
}

EdgeKind SemanticFacts::getEdgeKind(TokenKind kind) {
    switch (kind) {
        case TokenKind::EdgeKeyword: return EdgeKind::BothEdges;
        case TokenKind::PosEdgeKeyword: return EdgeKind::PosEdge;
        case TokenKind::NegEdgeKeyword: return EdgeKind::NegEdge;
        default: return EdgeKind::None;
    }
}

AssertionKind SemanticFacts::getAssertKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::ImmediateAssertStatement: return AssertionKind::Assert;
        case SyntaxKind::ImmediateAssumeStatement: return AssertionKind::Assume;
        case SyntaxKind::ImmediateCoverStatement: return AssertionKind::Cover;
        default: THROW_UNREACHABLE;
    }
}

ArgumentDirection SemanticFacts::getArgDirection(PortDirection direction) {
    switch (direction) {
        case PortDirection::In: return ArgumentDirection::In;
        case PortDirection::Out: return ArgumentDirection::Out;
        case PortDirection::InOut: return ArgumentDirection::InOut;
        case PortDirection::Ref: return ArgumentDirection::Ref;
        default: THROW_UNREACHABLE;
    }
}

GateType SemanticFacts::getGateType(TokenKind kind) {
    switch (kind) {
        case TokenKind::CmosKeyword: return GateType::Cmos;
        case TokenKind::RcmosKeyword: return GateType::Rcmos;
        case TokenKind::NmosKeyword: return GateType::Nmos;
        case TokenKind::PmosKeyword: return GateType::Pmos;
        case TokenKind::RnmosKeyword: return GateType::Rnmos;
        case TokenKind::RpmosKeyword: return GateType::Rpmos;
        case TokenKind::BufIf0Keyword: return GateType::BufIf0;
        case TokenKind::BufIf1Keyword: return GateType::BufIf1;
        case TokenKind::NotIf0Keyword: return GateType::NotIf0;
        case TokenKind::NotIf1Keyword: return GateType::NotIf1;
        case TokenKind::AndKeyword: return GateType::And;
        case TokenKind::NandKeyword: return GateType::Nand;
        case TokenKind::OrKeyword: return GateType::Or;
        case TokenKind::NorKeyword: return GateType::Nor;
        case TokenKind::XorKeyword: return GateType::Xor;
        case TokenKind::XnorKeyword: return GateType::Xnor;
        case TokenKind::BufKeyword: return GateType::Buf;
        case TokenKind::NotKeyword: return GateType::Not;
        case TokenKind::TranIf0Keyword: return GateType::TranIf0;
        case TokenKind::TranIf1Keyword: return GateType::TranIf1;
        case TokenKind::RtranIf0Keyword: return GateType::RtranIf0;
        case TokenKind::RtranIf1Keyword: return GateType::RtranIf1;
        case TokenKind::TranKeyword: return GateType::Tran;
        case TokenKind::RtranKeyword: return GateType::Rtran;
        case TokenKind::PullDownKeyword: return GateType::PullDown;
        case TokenKind::PullUpKeyword: return GateType::PullUp;
        default: THROW_UNREACHABLE;
    }
}

// clang-format on

StatementBlockKind SemanticFacts::getStatementBlockKind(const BlockStatementSyntax& syntax) {
    if (syntax.kind == SyntaxKind::SequentialBlockStatement)
        return StatementBlockKind::Sequential;

    ASSERT(syntax.kind == SyntaxKind::ParallelBlockStatement);
    switch (syntax.end.kind) {
        case TokenKind::JoinAnyKeyword:
            return StatementBlockKind::JoinAny;
        case TokenKind::JoinNoneKeyword:
            return StatementBlockKind::JoinNone;
        default:
            return StatementBlockKind::JoinAll;
    }
}

} // namespace slang

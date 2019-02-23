//------------------------------------------------------------------------------
// SemanticFacts.cpp
// Semantic enums and conversion methods.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/SemanticFacts.h"

namespace slang {

namespace SemanticFacts {

// clang-format off
std::optional<VariableLifetime> getVariableLifetime(Token token) {
    switch (token.kind) {
        case TokenKind::AutomaticKeyword: return VariableLifetime::Automatic;
        case TokenKind::StaticKeyword: return VariableLifetime::Static;
        case TokenKind::Unknown: return std::nullopt;
        default: THROW_UNREACHABLE;
    }
}

PortDirection getPortDirection(TokenKind kind) {
    switch (kind) {
        case TokenKind::InputKeyword: return PortDirection::In;
        case TokenKind::InOutKeyword: return PortDirection::InOut;
        case TokenKind::OutputKeyword: return PortDirection::Out;
        case TokenKind::RefKeyword: return PortDirection::Ref;
        default: return PortDirection::NotApplicable;
    }
}

ProceduralBlockKind getProceduralBlockKind(SyntaxKind kind) {
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

DefinitionKind getDefinitionKind(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::ModuleDeclaration: return DefinitionKind::Module;
        case SyntaxKind::InterfaceDeclaration: return DefinitionKind::Interface;
        case SyntaxKind::ProgramDeclaration: return DefinitionKind::Program;
        default: THROW_UNREACHABLE;
    }
}
// clang-format on

} // namespace SemanticFacts

} // namespace slang

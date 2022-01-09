//------------------------------------------------------------------------------
// CoverSymbols.cpp
// Contains coverage-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/CoverSymbols.h"

#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/SymbolBuilders.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"

namespace {

using namespace slang;

class OptionBuilder {
public:
    explicit OptionBuilder(const Scope& scope) : scope(scope) {}

    void add(const CoverageOptionSyntax& syntax) {
        options.emplace(scope, syntax);

        if (auto name = options.back().getName(); !name.empty()) {
            auto names = options.back().isTypeOption() ? &typeNames : &instNames;
            auto [it, inserted] = names->emplace(name, syntax.expr);
            if (!inserted) {
                auto& diag = scope.addDiag(diag::CoverageOptionDup, syntax.expr->sourceRange());
                diag << name;
                diag.addNote(diag::NotePreviousUsage, it->second->getFirstToken().location());
            }
        }
    }

    span<const CoverageOptionSetter> get() const { return options.copy(scope.getCompilation()); }

private:
    const Scope& scope;
    SmallVectorSized<CoverageOptionSetter, 4> options;
    SmallMap<string_view, const SyntaxNode*, 4> instNames;
    SmallMap<string_view, const SyntaxNode*, 4> typeNames;
};

} // namespace

namespace slang {

CoverageOptionSetter::CoverageOptionSetter(const Scope& scope, const CoverageOptionSyntax& syntax) :
    scope(scope), syntax(syntax) {
}

bool CoverageOptionSetter::isTypeOption() const {
    if (syntax.expr->kind == SyntaxKind::AssignmentExpression) {
        auto& assign = syntax.expr->as<BinaryExpressionSyntax>();
        if (assign.left->kind == SyntaxKind::ScopedName) {
            auto& scoped = assign.left->as<ScopedNameSyntax>();
            if (scoped.left->kind == SyntaxKind::IdentifierName) {
                return scoped.left->as<IdentifierNameSyntax>().identifier.valueText() ==
                       "type_option"sv;
            }
        }
    }
    return false;
}

string_view CoverageOptionSetter::getName() const {
    if (syntax.expr->kind == SyntaxKind::AssignmentExpression) {
        auto& assign = syntax.expr->as<BinaryExpressionSyntax>();
        if (assign.left->kind == SyntaxKind::ScopedName) {
            auto& scoped = assign.left->as<ScopedNameSyntax>();
            if (scoped.left->kind == SyntaxKind::IdentifierName &&
                scoped.right->kind == SyntaxKind::IdentifierName) {
                return scoped.right->as<IdentifierNameSyntax>().identifier.valueText();
            }
        }
    }
    return ""sv;
}

const Expression& CoverageOptionSetter::getExpression() const {
    if (!expr) {
        bitmask<BindFlags> flags = BindFlags::AssignmentAllowed;
        if (isTypeOption()) {
            flags |= BindFlags::StaticInitializer;
            flags |= BindFlags::Constant;
        }

        BindContext context(scope, LookupLocation(&scope, 3));
        expr = &Expression::bind(*syntax.expr, context, flags);
        context.setAttributes(*expr, syntax.attributes);
    }
    return *expr;
}

static void addProperty(Scope& scope, string_view name, VariableLifetime lifetime,
                        const StructBuilder& structBuilder) {
    auto& comp = scope.getCompilation();
    auto& prop = *comp.emplace<ClassPropertySymbol>(name, SourceLocation::NoLocation, lifetime,
                                                    Visibility::Public);
    prop.setType(structBuilder.type);
    scope.addMember(prop);
}

CovergroupBodySymbol::CovergroupBodySymbol(Compilation& comp, SourceLocation loc) :
    Symbol(SymbolKind::CovergroupBody, ""sv, loc), Scope(comp, this) {

    auto& int_t = comp.getIntType();
    auto& bit_t = comp.getBitType();
    auto& string_t = comp.getStringType();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("name"sv, string_t);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("auto_bin_max"sv, int_t);
    option.addField("cross_num_print_missing"sv, int_t);
    option.addField("detect_overlap"sv, bit_t);
    option.addField("per_instance"sv, bit_t);
    option.addField("get_inst_coverage"sv, bit_t);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    type_option.addField("strobe"sv, bit_t);
    type_option.addField("merge_instances"sv, bit_t);
    type_option.addField("distribute_first"sv, bit_t);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);
}

CovergroupType::CovergroupType(Compilation& compilation, string_view name, SourceLocation loc,
                               const CovergroupBodySymbol& body) :
    Type(SymbolKind::CovergroupType, name, loc),
    Scope(compilation, this), body(body) {
}

const Symbol& CovergroupType::fromSyntax(const Scope& scope,
                                         const CovergroupDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto body = comp.emplace<CovergroupBodySymbol>(comp, syntax.name.location());
    auto result =
        comp.emplace<CovergroupType>(comp, syntax.name.valueText(), syntax.name.location(), *body);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (syntax.portList) {
        SmallVectorSized<const FormalArgumentSymbol*, 8> args;
        SubroutineSymbol::buildArguments(*result, *syntax.portList, VariableLifetime::Automatic,
                                         args);
        result->arguments = args.copy(comp);

        for (auto arg : result->arguments) {
            if (arg->direction == ArgumentDirection::Out ||
                arg->direction == ArgumentDirection::InOut) {
                scope.addDiag(diag::CovergroupOutArg, arg->location);
            }
        }
    }

    result->addMember(*body);

    OptionBuilder options(*body);
    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::CoverageOption)
            options.add(member->as<CoverageOptionSyntax>());
        else
            body->addMembers(*member);
    }

    body->options = options.get();
    return *result;
}

const TimingControl* CovergroupType::getCoverageEvent() const {
    if (event)
        return *event;

    auto scope = getParentScope();
    auto syntax = getSyntax();
    if (scope && syntax) {
        if (auto evSyntax = syntax->as<CovergroupDeclarationSyntax>().event) {
            LookupLocation ll = LookupLocation::min;
            if (!arguments.empty())
                ll = LookupLocation::after(*arguments.back());

            BindContext context(*this, ll);

            if (evSyntax->kind == SyntaxKind::BlockCoverageEvent) {
                event = &BlockEventListControl::fromSyntax(
                    *evSyntax->as<BlockCoverageEventSyntax>().expr, context);
                return *event;
            }
            else if (evSyntax->kind == SyntaxKind::EventControlWithExpression) {
                event =
                    &TimingControl::bind(evSyntax->as<EventControlWithExpressionSyntax>(), context);
                return *event;
            }
        }
    }

    event = nullptr;
    return nullptr;
}

ConstantValue CovergroupType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

void CovergroupType::serializeTo(ASTSerializer&) const {
    // TODO:
}

CoverpointSymbol::CoverpointSymbol(Compilation& comp, string_view name, SourceLocation loc) :
    Symbol(SymbolKind::Coverpoint, name, loc), Scope(comp, this),
    declaredType(*this, DeclaredTypeFlags::InferImplicit | DeclaredTypeFlags::AutomaticInitializer |
                            DeclaredTypeFlags::CoverageType) {

    // Set the overrideIndex for the type and expression so that they cannot refer to
    // other members of the parent covergroup. This allows coverpoints named the same
    // as formal arguments to not interfere with lookup.
    declaredType.setOverrideIndex(SymbolIndex(1));

    auto& int_t = comp.getIntType();
    auto& bit_t = comp.getBitType();
    auto& string_t = comp.getStringType();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("auto_bin_max"sv, int_t);
    option.addField("detect_overlap"sv, bit_t);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);
}

CoverpointSymbol& CoverpointSymbol::fromSyntax(const Scope& scope, const CoverpointSyntax& syntax) {
    // It's possible for invalid syntax to parse as a coverpoint. If the keyword wasn't
    // given just give up and return a placeholder.
    auto& comp = scope.getCompilation();
    if (syntax.coverpoint.isMissing())
        return *comp.emplace<CoverpointSymbol>(comp, ""sv, syntax.getFirstToken().location());

    // Figure out the name of the coverpoint. If there's a label, it provides the name.
    // Otherwise check if the expression is a simple variable reference. If so, we take
    // that variable name as the name of the coverpoint. Otherwise it's unnamed.
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        name = syntax.label->name.valueText();
        loc = syntax.label->name.location();
    }
    else if (syntax.expr->kind == SyntaxKind::IdentifierName) {
        auto id = syntax.expr->as<IdentifierNameSyntax>().identifier;
        name = id.valueText();
        loc = id.location();
    }
    else {
        loc = syntax.expr->getFirstToken().location();
    }

    auto result = comp.emplace<CoverpointSymbol>(comp, name, loc);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    result->declaredType.setTypeSyntax(*syntax.type);
    result->declaredType.setInitializerSyntax(*syntax.expr,
                                              syntax.expr->getFirstToken().location());

    return *result;
}

CoverpointSymbol& CoverpointSymbol::fromImplicit(const Scope& scope,
                                                 const IdentifierNameSyntax& syntax) {
    auto loc = syntax.identifier.location();
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverpointSymbol>(comp, syntax.identifier.valueText(), loc);

    result->declaredType.setTypeSyntax(comp.createEmptyTypeSyntax(loc));
    result->declaredType.setInitializerSyntax(syntax, loc);
    return *result;
}

const Expression* CoverpointSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        ASSERT(scope);

        if (!syntax)
            iffExpr = nullptr;
        else {
            auto iffSyntax = syntax->as<CoverpointSyntax>().iff;
            if (!iffSyntax)
                iffExpr = nullptr;
            else {
                BindContext context(*scope, LookupLocation::min);
                iffExpr = &Expression::bind(*iffSyntax->expr, context);
                context.requireBooleanConvertible(*iffExpr.value());
            }
        }
    }
    return *iffExpr;
}

void CoverpointSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

CoverCrossSymbol::CoverCrossSymbol(Compilation& comp, string_view name, SourceLocation loc,
                                   span<const CoverpointSymbol* const> targets) :
    Symbol(SymbolKind::CoverCross, name, loc),
    Scope(comp, this), targets(targets) {

    auto& int_t = comp.getIntType();
    auto& string_t = comp.getStringType();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("cross_num_print_missing"sv, int_t);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);
}

void CoverCrossSymbol::fromSyntax(const Scope& scope, const CoverCrossSyntax& syntax,
                                  SmallVector<const Symbol*>& results) {
    string_view name;
    SourceLocation loc;
    if (syntax.label) {
        name = syntax.label->name.valueText();
        loc = syntax.label->name.location();
    }
    else {
        loc = syntax.cross.location();
    }

    SmallVectorSized<const CoverpointSymbol*, 4> targets;
    for (auto item : syntax.items) {
        auto symbol = scope.find(item->identifier.valueText());
        if (symbol && symbol->kind == SymbolKind::Coverpoint) {
            targets.append(&symbol->as<CoverpointSymbol>());
        }
        else {
            // If we didn't find a coverpoint, create one implicitly
            // that will be initialized with this expression.
            auto& newPoint = CoverpointSymbol::fromImplicit(scope, *item);
            targets.append(&newPoint);
            results.append(&newPoint);
        }
    }

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverCrossSymbol>(comp, name, loc, targets.copy(comp));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    results.append(result);
}

const Expression* CoverCrossSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        ASSERT(scope);

        if (!syntax)
            iffExpr = nullptr;
        else {
            auto iffSyntax = syntax->as<CoverCrossSyntax>().iff;
            if (!iffSyntax)
                iffExpr = nullptr;
            else {
                BindContext context(*scope, LookupLocation::min);
                iffExpr = &Expression::bind(*iffSyntax->expr, context);
                context.requireBooleanConvertible(*iffExpr.value());
            }
        }
    }
    return *iffExpr;
}

void CoverCrossSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

} // namespace slang

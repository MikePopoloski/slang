//------------------------------------------------------------------------------
// CoverSymbols.cpp
// Contains coverage-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/CoverSymbols.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/SymbolBuilders.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::ast;

class OptionBuilder {
public:
    explicit OptionBuilder(const Scope& scope) : scope(scope) {}

    void add(const CoverageOptionSyntax& syntax) {
        options.emplace_back(scope, syntax);

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

    std::span<const CoverageOptionSetter> get() const {
        return options.copy(scope.getCompilation());
    }

private:
    const Scope& scope;
    SmallVector<CoverageOptionSetter, 4> options;
    SmallMap<std::string_view, const SyntaxNode*, 4> instNames;
    SmallMap<std::string_view, const SyntaxNode*, 4> typeNames;
};

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

CoverageOptionSetter::CoverageOptionSetter(const Scope& scope, const CoverageOptionSyntax& syntax) :
    scope(&scope), syntax(&syntax) {
}

bool CoverageOptionSetter::isTypeOption() const {
    if (syntax->expr->kind == SyntaxKind::AssignmentExpression) {
        auto& assign = syntax->expr->as<BinaryExpressionSyntax>();
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

std::string_view CoverageOptionSetter::getName() const {
    if (syntax->expr->kind == SyntaxKind::AssignmentExpression) {
        auto& assign = syntax->expr->as<BinaryExpressionSyntax>();
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
        bitmask<ASTFlags> flags = ASTFlags::AssignmentAllowed;
        bool isTypeOpt = isTypeOption();
        if (isTypeOpt)
            flags |= ASTFlags::StaticInitializer;

        ASTContext context(*scope, LookupLocation(scope, 3));
        expr = &Expression::bind(*syntax->expr, context, flags);
        context.setAttributes(*expr, syntax->attributes);

        if (isTypeOpt && expr->kind == ExpressionKind::Assignment)
            context.eval(expr->as<AssignmentExpression>().right());
    }
    return *expr;
}

void CoverageOptionSetter::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", getExpression());
}

static void addProperty(Scope& scope, std::string_view name, VariableLifetime lifetime,
                        const StructBuilder& structBuilder) {
    auto& comp = scope.getCompilation();
    auto& prop = *comp.emplace<ClassPropertySymbol>(name, SourceLocation::NoLocation, lifetime,
                                                    Visibility::Public);
    prop.setType(structBuilder.type);
    scope.addMember(prop);
}

static void addBuiltInMethods(Scope& scope, bool isCovergroup) {
    auto& comp = scope.getCompilation();
    auto makeFunc = [&](std::string_view funcName, const Type& returnType) {
        MethodBuilder builder(comp, funcName, returnType, SubroutineKind::Function);
        scope.addMember(builder.symbol);
        return builder;
    };

    auto& void_t = comp.getVoidType();
    auto& int_t = comp.getIntType();
    auto& real_t = comp.getRealType();
    auto& string_t = comp.getStringType();

    if (isCovergroup)
        makeFunc("set_inst_name"sv, void_t).addArg("name"sv, string_t);

    auto get_coverage = makeFunc("get_coverage"sv, real_t);
    get_coverage.addFlags(MethodFlags::Static);
    get_coverage.addArg("covered_bins"sv, int_t, ArgumentDirection::Ref, SVInt(32, 0, true));
    get_coverage.addArg("total_bins"sv, int_t, ArgumentDirection::Ref, SVInt(32, 0, true));

    auto get_inst_coverage = makeFunc("get_inst_coverage"sv, real_t);
    get_inst_coverage.addArg("covered_bins"sv, int_t, ArgumentDirection::Ref, SVInt(32, 0, true));
    get_inst_coverage.addArg("total_bins"sv, int_t, ArgumentDirection::Ref, SVInt(32, 0, true));

    makeFunc("start"sv, void_t);
    makeFunc("stop"sv, void_t);
}

CovergroupBodySymbol::CovergroupBodySymbol(Compilation& comp, SourceLocation loc) :
    Symbol(SymbolKind::CovergroupBody, ""sv, loc), Scope(comp, this) {

    auto& int_t = comp.getIntType();
    auto& bit_t = comp.getBitType();
    auto& string_t = comp.getStringType();
    auto& real_t = comp.getRealType();
    auto lv = comp.languageVersion();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("name"sv, string_t);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("auto_bin_max"sv, int_t, VariableFlags::ImmutableCoverageOption);
    option.addField("cross_num_print_missing"sv, int_t);
    if (lv >= LanguageVersion::v1800_2023)
        option.addField("cross_retain_auto_bins"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    option.addField("detect_overlap"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    option.addField("per_instance"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    option.addField("get_inst_coverage"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    type_option.addField("strobe"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    type_option.addField("merge_instances"sv, bit_t);
    type_option.addField("distribute_first"sv, bit_t);
    if (lv >= LanguageVersion::v1800_2023)
        type_option.addField("real_interval"sv, real_t, VariableFlags::ImmutableCoverageOption);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);

    addBuiltInMethods(*this, true);

    lastBuiltinMember = getLastMember();
}

void CovergroupBodySymbol::serializeTo(ASTSerializer& serializer) const {
    if (!options.empty()) {
        serializer.startArray("options");
        for (auto& opt : options) {
            serializer.startObject();
            opt.serializeTo(serializer);
            serializer.endObject();
        }
        serializer.endArray();
    }
}

CovergroupType::CovergroupType(Compilation& compilation, std::string_view name, SourceLocation loc,
                               const CovergroupBodySymbol& body) :
    Type(SymbolKind::CovergroupType, name, loc), Scope(compilation, this), body(body) {
}

const CovergroupType& CovergroupType::fromSyntax(const Scope& scope,
                                                 const CovergroupDeclarationSyntax& syntax,
                                                 const Symbol*& classProperty) {
    // If we're inside a class, this covergroup is actually anonymous and the name
    // is used to implicitly declare a property of the covergroup type.
    bool inClass = scope.asSymbol().kind == SymbolKind::ClassType;
    std::string_view name = inClass ? ""sv : syntax.name.valueText();

    auto& comp = scope.getCompilation();
    auto body = comp.emplace<CovergroupBodySymbol>(comp, syntax.name.location());
    auto result = comp.emplace<CovergroupType>(comp, name, syntax.name.location(), *body);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (!syntax.extends) {
        if (syntax.portList) {
            SmallVector<const FormalArgumentSymbol*> args;
            SubroutineSymbol::buildArguments(*result, scope, *syntax.portList,
                                             VariableLifetime::Automatic, args);
            result->arguments = args.copy(comp);

            for (auto arg : result->arguments) {
                if (arg->direction == ArgumentDirection::Out ||
                    arg->direction == ArgumentDirection::InOut) {
                    scope.addDiag(diag::CovergroupOutArg, arg->location);
                }
            }
        }

        MethodBuilder sample(comp, "sample"sv, comp.getVoidType(), SubroutineKind::Function);
        body->addMember(sample.symbol);

        if (syntax.event && syntax.event->kind == SyntaxKind::WithFunctionSample) {
            auto& wfs = syntax.event->as<WithFunctionSampleSyntax>();
            if (wfs.portList) {
                SmallVector<const FormalArgumentSymbol*> args;
                SubroutineSymbol::buildArguments(*result, scope, *wfs.portList,
                                                 VariableLifetime::Automatic, args);

                for (auto arg : args) {
                    if (arg->direction == ArgumentDirection::Out ||
                        arg->direction == ArgumentDirection::InOut) {
                        scope.addDiag(diag::CovergroupOutArg, arg->location);
                    }

                    const_cast<FormalArgumentSymbol*>(arg)->flags |=
                        VariableFlags::CoverageSampleFormal;
                    sample.copyArg(*arg);
                }
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

    if (inClass) {
        auto var = comp.emplace<ClassPropertySymbol>(syntax.name.valueText(),
                                                     syntax.name.location(),
                                                     VariableLifetime::Automatic,
                                                     Visibility::Public);
        var->setType(*result);
        var->flags |= VariableFlags::Const;
        classProperty = var;

        if (syntax.extends)
            result->setNeedElaboration();
    }

    return *result;
}

void CovergroupType::inheritMembers(function_ref<void(const Symbol&)> insertCB) const {
    auto syntax = getSyntax();
    auto scope = getParentScope();
    SLANG_ASSERT(syntax && scope);

    // If this covergroup doesn't inherit from anything then there's nothing to do.
    auto& cds = syntax->as<CovergroupDeclarationSyntax>();
    if (!cds.extends)
        return;

    auto& comp = scope->getCompilation();
    baseGroup = &comp.getErrorType();

    // Find the base class's group from which we are inheriting.
    auto baseClass = scope->asSymbol().as<ClassType>().getBaseClass();
    if (!baseClass || baseClass->kind != SymbolKind::ClassType)
        return;

    auto baseName = cds.name.valueText();
    auto candidateBase = baseClass->as<ClassType>().find(baseName);
    if (candidateBase && candidateBase->kind == SymbolKind::ClassProperty) {
        auto& ct = candidateBase->as<ClassPropertySymbol>().getType();
        if (ct.kind == SymbolKind::CovergroupType)
            baseGroup = &ct;
    }

    if (baseGroup->isError()) {
        if (!baseName.empty()) {
            scope->addDiag(diag::UnknownCovergroupBase, cds.name.range())
                << baseName << baseClass->name;
        }
        return;
    }

    auto& baseCG = baseGroup->as<CovergroupType>();
    arguments = baseCG.getArguments();
    event = baseCG.event;

    // We have the base group -- inherit all of the members from it.
    auto& scopeNameMap = body.getUnelaboratedNameMap();
    for (auto& member : baseCG.getBody().members()) {
        if (member.name.empty())
            continue;

        // Don't inherit if the member is already overridden.
        if (auto it = scopeNameMap.find(member.name); it != scopeNameMap.end())
            continue;

        // If the symbol itself was already inherited, create a new wrapper around
        // it for our own scope.
        const Symbol* toWrap = &member;
        if (member.kind == SymbolKind::TransparentMember)
            toWrap = &member.as<TransparentMemberSymbol>().wrapped;

        // All symbols get inserted into the beginning of the scope using the
        // provided insertion callback. We insert them as TransparentMemberSymbols
        // so that we can trace a path back to the actual location they are declared.
        auto wrapper = comp.emplace<TransparentMemberSymbol>(*toWrap);
        body.insertMember(wrapper, body.lastBuiltinMember, true, false);
    }

    // Also inherit any argument symbols are in the base covergroup type itself,
    // as opposed to the body which we already looked at above.
    for (auto& member : baseCG.members()) {
        const Symbol* toWrap = &member;
        if (member.kind == SymbolKind::TransparentMember)
            toWrap = &member.as<TransparentMemberSymbol>().wrapped;

        if (toWrap->kind == SymbolKind::FormalArgument) {
            auto wrapper = comp.emplace<TransparentMemberSymbol>(*toWrap);
            insertCB(*wrapper);
        }
    }
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

            ASTContext context(*this, ll);

            if (evSyntax->kind == SyntaxKind::BlockCoverageEvent) {
                event = &BlockEventListControl::fromSyntax(
                    *evSyntax->as<BlockCoverageEventSyntax>().expr, context);
                return *event;
            }
            else if (evSyntax->kind == SyntaxKind::EventControlWithExpression) {
                event = &TimingControl::bind(evSyntax->as<EventControlWithExpressionSyntax>(),
                                             context);
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

void CovergroupType::serializeTo(ASTSerializer& serializer) const {
    if (auto ev = getCoverageEvent())
        serializer.write("event", *ev);
    if (auto bg = getBaseGroup())
        serializer.writeLink("baseGroup", *bg);
}

const Expression* CoverageBinSymbol::getIffExpr() const {
    if (!isResolved)
        resolve();
    return iffExpr;
}

const Expression* CoverageBinSymbol::getNumberOfBinsExpr() const {
    if (!isResolved)
        resolve();
    return numberOfBinsExpr;
}

const Expression* CoverageBinSymbol::getSetCoverageExpr() const {
    if (!isResolved)
        resolve();
    return setCoverageExpr;
}

const Expression* CoverageBinSymbol::getWithExpr() const {
    if (!isResolved)
        resolve();
    return withExpr;
}

const BinsSelectExpr* CoverageBinSymbol::getCrossSelectExpr() const {
    if (!isResolved)
        resolve();
    return selectExpr;
}

std::span<const Expression* const> CoverageBinSymbol::getValues() const {
    if (!isResolved)
        resolve();
    return values;
}

std::span<const CoverageBinSymbol::TransSet> CoverageBinSymbol::getTransList() const {
    if (!isResolved)
        resolve();
    return transList;
}

void CoverageBinSymbol::serializeTo(ASTSerializer& serializer) const {
    switch (binsKind) {
        case Bins:
            serializer.write("binsKind"sv, "Bins"sv);
            break;
        case IllegalBins:
            serializer.write("binsKind"sv, "IllegalBins"sv);
            break;
        case IgnoreBins:
            serializer.write("binsKind"sv, "IgnoreBins"sv);
            break;
    }

    serializer.write("isArray", isArray);
    serializer.write("isWildcard", isWildcard);
    serializer.write("isDefault", isDefault);
    serializer.write("isDefaultSequence", isDefaultSequence);

    if (auto expr = getIffExpr())
        serializer.write("iff", *expr);

    if (auto expr = getNumberOfBinsExpr())
        serializer.write("numberOfBins", *expr);

    if (auto expr = getSetCoverageExpr())
        serializer.write("setCoverage", *expr);

    if (auto expr = getWithExpr())
        serializer.write("with", *expr);

    if (auto expr = getCrossSelectExpr())
        serializer.write("crossSelect", *expr);

    auto valArray = getValues();
    if (!valArray.empty()) {
        serializer.startArray("values");
        for (auto val : valArray)
            serializer.serialize(*val);
        serializer.endArray();
    }

    auto trans = getTransList();
    if (!trans.empty()) {
        serializer.startArray("trans");
        for (auto& set : trans) {
            serializer.startArray();
            for (auto& rangeList : set) {
                serializer.startObject();
                rangeList.serializeTo(serializer);
                serializer.endObject();
            }
            serializer.endArray();
        }
        serializer.endArray();
    }
}

CoverageBinSymbol& CoverageBinSymbol::fromSyntax(const Scope& scope,
                                                 const CoverageBinsSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverageBinSymbol>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    result->isWildcard = syntax.wildcard.kind == TokenKind::WildcardKeyword;

    if (syntax.keyword.kind == TokenKind::IgnoreBinsKeyword)
        result->binsKind = IgnoreBins;
    else if (syntax.keyword.kind == TokenKind::IllegalBinsKeyword)
        result->binsKind = IllegalBins;

    if (syntax.size)
        result->isArray = true;

    if (syntax.initializer->kind == SyntaxKind::DefaultCoverageBinInitializer) {
        result->isDefault = true;
        if (syntax.initializer->as<DefaultCoverageBinInitializerSyntax>().sequenceKeyword)
            result->isDefaultSequence = true;
    }

    return *result;
}

CoverageBinSymbol& CoverageBinSymbol::fromSyntax(const Scope& scope,
                                                 const BinsSelectionSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverageBinSymbol>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    if (syntax.keyword.kind == TokenKind::IgnoreBinsKeyword)
        result->binsKind = IgnoreBins;
    else if (syntax.keyword.kind == TokenKind::IllegalBinsKeyword)
        result->binsKind = IllegalBins;

    return *result;
}

static const Expression& bindCovergroupExpr(const ExpressionSyntax& syntax,
                                            const ASTContext& context,
                                            const Type* lvalueType = nullptr,
                                            bitmask<ASTFlags> extraFlags = {}) {
    const Expression* expr;
    if (lvalueType)
        expr = &Expression::bindRValue(*lvalueType, syntax, {}, context, extraFlags);
    else
        expr = &Expression::bind(syntax, context, extraFlags);

    context.eval(*expr, EvalFlags::CovergroupExpr);
    return *expr;
}

static const Expression* bindIffExpr(const CoverageIffClauseSyntax* syntax,
                                     const ASTContext& context) {
    if (!syntax)
        return nullptr;

    auto& result = Expression::bind(*syntax->expr, context, ASTFlags::AllowCoverageSampleFormal);
    context.requireBooleanConvertible(result);
    return &result;
}

void CoverageBinSymbol::resolve() const {
    SLANG_ASSERT(!isResolved);
    isResolved = true;

    auto syntax = getSyntax();
    auto scope = getParentScope();
    SLANG_ASSERT(syntax && scope);

    auto& comp = scope->getCompilation();
    ASTContext context(*scope, LookupLocation::before(*this));

    if (syntax->kind == SyntaxKind::BinsSelection) {
        auto& binsSyntax = syntax->as<BinsSelectionSyntax>();
        iffExpr = bindIffExpr(binsSyntax.iff, context);
        selectExpr = &BinsSelectExpr::bind(*binsSyntax.expr, context);
        return;
    }

    auto& coverpoint = scope->asSymbol().as<CoverpointSymbol>();
    auto& type = coverpoint.getType();

    auto& binsSyntax = syntax->as<CoverageBinsSyntax>();
    iffExpr = bindIffExpr(binsSyntax.iff, context);

    if (binsSyntax.size && binsSyntax.size->expr) {
        numberOfBinsExpr = &bindCovergroupExpr(*binsSyntax.size->expr, context);
        context.requireIntegral(*numberOfBinsExpr);
    }

    if (isWildcard && type.isFloating())
        context.addDiag(diag::RealCoverpointWildcardBins, binsSyntax.wildcard.range());

    auto bindWithExpr = [&](const WithClauseSyntax& withSyntax) {
        // Create the iterator variable and set it up with an AST context so that it
        // can be found by the iteration expression.
        auto arrayType = comp.emplace<DynamicArrayType>(type);
        auto it = comp.emplace<IteratorSymbol>(*context.scope, "item"sv, coverpoint.location,
                                               *arrayType, ""sv);

        ASTContext iterCtx = context;
        it->nextTemp = std::exchange(iterCtx.firstTempVar, it);

        withExpr = &bindCovergroupExpr(*withSyntax.expr, iterCtx);
        iterCtx.requireBooleanConvertible(*withExpr);

        if (type.isFloating())
            context.addDiag(diag::RealCoverpointWithExpr, withSyntax.sourceRange());
    };

    auto init = binsSyntax.initializer;
    switch (init->kind) {
        case SyntaxKind::RangeCoverageBinInitializer: {
            SmallVector<const Expression*> buffer;
            auto& rcbis = init->as<RangeCoverageBinInitializerSyntax>();
            for (auto elem : rcbis.ranges->valueRanges)
                buffer.push_back(&bindCovergroupExpr(*elem, context, &type));
            values = buffer.copy(comp);

            if (rcbis.withClause)
                bindWithExpr(*rcbis.withClause);
            break;
        }
        case SyntaxKind::IdWithExprCoverageBinInitializer: {
            auto& iwecbi = init->as<IdWithExprCoverageBinInitializerSyntax>();
            bindWithExpr(*iwecbi.withClause);

            auto targetName = iwecbi.id.valueText();
            if (!targetName.empty() && targetName != coverpoint.name)
                context.addDiag(diag::CoverageBinTargetName, iwecbi.id.range());
            break;
        }
        case SyntaxKind::TransListCoverageBinInitializer: {
            SmallVector<TransSet, 4> listBuffer;
            for (auto setElem : init->as<TransListCoverageBinInitializerSyntax>().sets) {
                SmallVector<TransRangeList, 4> setBuffer;
                for (auto rangeElem : setElem->ranges)
                    setBuffer.emplace_back(*rangeElem, type, context);
                listBuffer.push_back(setBuffer.copy(comp));
            }
            transList = listBuffer.copy(comp);

            if (type.isFloating())
                context.addDiag(diag::RealCoverpointTransBins, init->sourceRange());

            break;
        }
        case SyntaxKind::ExpressionCoverageBinInitializer:
            setCoverageExpr = &bindCovergroupExpr(
                *init->as<ExpressionCoverageBinInitializerSyntax>().expr, context);

            if (!setCoverageExpr->bad()) {
                auto& t = *setCoverageExpr->type;
                if (!t.isArray() || t.isAssociativeArray() ||
                    !type.isAssignmentCompatible(*t.getArrayElementType())) {

                    auto& diag = context.addDiag(diag::CoverageSetType,
                                                 setCoverageExpr->sourceRange);
                    diag << t << type;
                }
            }
            break;
        case SyntaxKind::DefaultCoverageBinInitializer:
            if (binsSyntax.size && type.isFloating())
                context.addDiag(diag::RealCoverpointDefaultArray, binsSyntax.size->sourceRange());
            break;
        default:
            SLANG_UNREACHABLE;
    }
}

CoverageBinSymbol::TransRangeList::TransRangeList(const TransRangeSyntax& syntax, const Type& type,
                                                  const ASTContext& context) {
    SmallVector<const Expression*> buffer;
    for (auto elem : syntax.items) {
        auto& expr = bindCovergroupExpr(*elem, context, &type);
        buffer.push_back(&expr);
    }

    auto& comp = context.getCompilation();
    items = buffer.copy(comp);

    if (syntax.repeat) {
        switch (syntax.repeat->specifier.kind) {
            case TokenKind::Star:
                repeatKind = Consecutive;
                break;
            case TokenKind::Equals:
                repeatKind = Nonconsecutive;
                break;
            case TokenKind::MinusArrow:
                repeatKind = GoTo;
                break;
            default:
                SLANG_UNREACHABLE;
        }

        auto bindCount = [&](const ExpressionSyntax& exprSyntax) {
            auto& expr = bindCovergroupExpr(exprSyntax, context);
            context.requireIntegral(expr);
            return &expr;
        };

        if (auto sel = syntax.repeat->selector) {
            if (sel->kind == SyntaxKind::BitSelect) {
                repeatFrom = bindCount(*sel->as<BitSelectSyntax>().expr);
            }
            else {
                auto& rss = sel->as<RangeSelectSyntax>();
                repeatFrom = bindCount(*rss.left);
                repeatTo = bindCount(*rss.right);
            }
        }
    }
}

void CoverageBinSymbol::TransRangeList::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("items");
    for (auto item : items)
        serializer.serialize(*item);
    serializer.endArray();

    if (repeatFrom)
        serializer.write("repeatFrom", *repeatFrom);
    if (repeatTo)
        serializer.write("repeatTo", *repeatTo);

    switch (repeatKind) {
        case Consecutive:
            serializer.write("repeatKind", "Consecutive"sv);
            break;
        case Nonconsecutive:
            serializer.write("repeatKind", "Nonconsecutive"sv);
            break;
        case GoTo:
            serializer.write("repeatKind", "GoTo"sv);
            break;
        default:
            break;
    }
}

CoverpointSymbol::CoverpointSymbol(Compilation& comp, std::string_view name, SourceLocation loc) :
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
    auto& real_t = comp.getRealType();
    auto lv = comp.languageVersion();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("auto_bin_max"sv, int_t, VariableFlags::ImmutableCoverageOption);
    option.addField("detect_overlap"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    if (lv >= LanguageVersion::v1800_2023)
        type_option.addField("real_interval"sv, real_t, VariableFlags::ImmutableCoverageOption);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);

    addBuiltInMethods(*this, false);
}

CoverpointSymbol& CoverpointSymbol::fromSyntax(const Scope& scope, const CoverpointSyntax& syntax) {
    // It's possible for invalid syntax to parse as a coverpoint. If the keyword wasn't
    // given just give up and return a placeholder.
    auto& comp = scope.getCompilation();
    if (syntax.coverpoint.isMissing()) {
        auto result = comp.emplace<CoverpointSymbol>(comp, ""sv, syntax.getFirstToken().location());
        result->declaredType.setType(comp.getErrorType());
        return *result;
    }

    // Figure out the name of the coverpoint. If there's a label, it provides the name.
    // Otherwise check if the expression is a simple variable reference. If so, we take
    // that variable name as the name of the coverpoint. Otherwise it's unnamed.
    std::string_view name;
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

    OptionBuilder options(*result);
    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::CoverageOption)
            options.add(member->as<CoverageOptionSyntax>());
        else
            result->addMembers(*member);
    }

    result->options = options.get();
    return *result;
}

CoverpointSymbol& CoverpointSymbol::fromImplicit(const Scope& scope,
                                                 const IdentifierNameSyntax& syntax) {
    auto loc = syntax.identifier.location();
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverpointSymbol>(comp, syntax.identifier.valueText(), loc);

    result->isImplicit = true;
    result->declaredType.setTypeSyntax(comp.createEmptyTypeSyntax(loc));
    result->declaredType.setInitializerSyntax(syntax, loc);
    return *result;
}

const Expression* CoverpointSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        SLANG_ASSERT(scope);

        if (!syntax) {
            iffExpr = nullptr;
        }
        else {
            ASTContext context(*scope, LookupLocation::min);
            iffExpr = bindIffExpr(syntax->as<CoverpointSyntax>().iff, context);
        }
    }
    return *iffExpr;
}

void CoverpointSymbol::checkBins() const {
    if (getType().isFloating()) {
        auto scope = getParentScope();
        SLANG_ASSERT(scope);

        if (isImplicit && !name.empty()) {
            scope->addDiag(diag::RealCoverpointImplicit, location) << name;
        }
        else if (membersOfType<CoverageBinSymbol>().empty()) {
            if (scope->getCompilation().languageVersion() >= LanguageVersion::v1800_2023)
                scope->addDiag(diag::RealCoverpointBins, location);
        }
    }
}

void CoverpointSymbol::serializeTo(ASTSerializer& serializer) const {
    if (!options.empty()) {
        serializer.startArray("options");
        for (auto& opt : options) {
            serializer.startObject();
            opt.serializeTo(serializer);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (auto iff = getIffExpr())
        serializer.write("iff", *iff);
}

CoverCrossSymbol::CoverCrossSymbol(Compilation& comp, std::string_view name, SourceLocation loc,
                                   std::span<const CoverpointSymbol* const> targets) :
    Symbol(SymbolKind::CoverCross, name, loc), Scope(comp, this), targets(targets) {

    auto& bit_t = comp.getBitType();
    auto& int_t = comp.getIntType();
    auto& string_t = comp.getStringType();
    auto lv = comp.languageVersion();

    StructBuilder option(*this, LookupLocation::min);
    option.addField("weight"sv, int_t);
    option.addField("goal"sv, int_t);
    option.addField("comment"sv, string_t);
    option.addField("at_least"sv, int_t);
    option.addField("cross_num_print_missing"sv, int_t);
    if (lv >= LanguageVersion::v1800_2023)
        option.addField("cross_retain_auto_bins"sv, bit_t, VariableFlags::ImmutableCoverageOption);
    addProperty(*this, "option"sv, VariableLifetime::Automatic, option);

    StructBuilder type_option(*this, LookupLocation::min);
    type_option.addField("weight"sv, int_t);
    type_option.addField("goal"sv, int_t);
    type_option.addField("comment"sv, string_t);
    addProperty(*this, "type_option"sv, VariableLifetime::Static, type_option);

    addBuiltInMethods(*this, false);
}

CoverCrossSymbol& CoverCrossSymbol::fromSyntax(const Scope& scope, const CoverCrossSyntax& syntax,
                                               SmallVectorBase<const Symbol*>& implicitMembers) {
    std::string_view name;
    SourceLocation loc;
    if (syntax.label) {
        name = syntax.label->name.valueText();
        loc = syntax.label->name.location();
    }
    else {
        loc = syntax.cross.location();
    }

    SmallVector<const CoverpointSymbol*> targets;
    for (auto item : syntax.items) {
        auto symbol = scope.find(item->identifier.valueText());
        if (symbol && symbol->kind == SymbolKind::Coverpoint) {
            targets.push_back(&symbol->as<CoverpointSymbol>());
        }
        else {
            // If we didn't find a coverpoint, create one implicitly
            // that will be initialized with this expression.
            auto& newPoint = CoverpointSymbol::fromImplicit(scope, *item);
            targets.push_back(&newPoint);
            implicitMembers.push_back(&newPoint);
        }
    }

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<CoverCrossSymbol>(comp, name, loc, targets.copy(comp));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

void CoverCrossSymbol::addBody(const syntax::CoverCrossSyntax& syntax, const Scope& scope) {
    auto& comp = scope.getCompilation();
    auto body = comp.emplace<CoverCrossBodySymbol>(comp, location);
    addMember(*body);

    StructBuilder valType(*body, LookupLocation::min);
    for (auto item : targets)
        valType.addField(item->name, item->declaredType.getType());

    auto valType_t = comp.emplace<TypeAliasType>("CrossValType", location);
    valType_t->targetType.setType(valType.type);
    body->addMember(*valType_t);

    auto queueType = comp.emplace<QueueType>(*valType_t, 0u);
    auto queueType_t = comp.emplace<TypeAliasType>("CrossQueueType", location);
    queueType_t->targetType.setType(*queueType);
    body->addMember(*queueType_t);
    body->crossQueueType = queueType_t;

    OptionBuilder optionBuilder(*this);
    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::CoverageOption)
            optionBuilder.add(member->as<CoverageOptionSyntax>());
        else
            body->addMembers(*member);
    }

    options = optionBuilder.get();
}

const Expression* CoverCrossSymbol::getIffExpr() const {
    if (!iffExpr) {
        auto scope = getParentScope();
        auto syntax = getSyntax();
        SLANG_ASSERT(scope);

        if (!syntax) {
            iffExpr = nullptr;
        }
        else {
            ASTContext context(*scope, LookupLocation::min);
            iffExpr = bindIffExpr(syntax->as<CoverCrossSyntax>().iff, context);
        }
    }
    return *iffExpr;
}

void CoverCrossSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("targets");
    for (auto target : targets) {
        serializer.startObject();
        serializer.writeLink("coverpoint", *target);
        serializer.endObject();
    }
    serializer.endArray();

    if (!options.empty()) {
        serializer.startArray("options");
        for (auto& opt : options) {
            serializer.startObject();
            opt.serializeTo(serializer);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (auto iff = getIffExpr())
        serializer.write("iff", *iff);
}

const BinsSelectExpr& BinsSelectExpr::bind(const BinsSelectExpressionSyntax& syntax,
                                           const ASTContext& context) {
    BinsSelectExpr* result;
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedBinsSelectExpr:
            return bind(*syntax.as<ParenthesizedBinsSelectExprSyntax>().expr, context);
        case SyntaxKind::BinsSelectConditionExpr:
            result = &ConditionBinsSelectExpr::fromSyntax(
                syntax.as<BinsSelectConditionExprSyntax>(), context);
            break;
        case SyntaxKind::UnaryBinsSelectExpr:
            result = &UnaryBinsSelectExpr::fromSyntax(syntax.as<UnaryBinsSelectExprSyntax>(),
                                                      context);
            break;
        case SyntaxKind::BinaryBinsSelectExpr:
            result = &BinaryBinsSelectExpr::fromSyntax(syntax.as<BinaryBinsSelectExprSyntax>(),
                                                       context);
            break;
        case SyntaxKind::SimpleBinsSelectExpr:
            result = &SetExprBinsSelectExpr::fromSyntax(syntax.as<SimpleBinsSelectExprSyntax>(),
                                                        context);
            break;
        case SyntaxKind::BinSelectWithFilterExpr:
            result = &BinSelectWithFilterExpr::fromSyntax(
                syntax.as<BinSelectWithFilterExprSyntax>(), context);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

BinsSelectExpr& BinsSelectExpr::badExpr(Compilation& compilation, const BinsSelectExpr* expr) {
    return *compilation.emplace<InvalidBinsSelectExpr>(expr);
}

void InvalidBinsSelectExpr::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

BinsSelectExpr& ConditionBinsSelectExpr::fromSyntax(const BinsSelectConditionExprSyntax& syntax,
                                                    const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& nameExpr = Expression::bind(*syntax.name, context, ASTFlags::AllowCoverpoint);
    if (nameExpr.bad())
        return badExpr(comp, nullptr);

    auto sym = nameExpr.getSymbolReference();
    if (!sym || (sym->kind != SymbolKind::Coverpoint &&
                 (sym->kind != SymbolKind::CoverageBin ||
                  sym->getParentScope()->asSymbol().kind != SymbolKind::Coverpoint))) {
        context.addDiag(diag::InvalidBinsTarget, syntax.name->sourceRange());
        return badExpr(comp, nullptr);
    }

    auto expr = comp.emplace<ConditionBinsSelectExpr>(*sym);

    if (syntax.intersects) {
        const Type* type;
        if (sym->kind == SymbolKind::Coverpoint)
            type = &sym->as<CoverpointSymbol>().declaredType.getType();
        else
            type = &sym->getParentScope()->asSymbol().as<CoverpointSymbol>().declaredType.getType();

        SmallVector<const Expression*> buffer;
        for (auto elem : syntax.intersects->ranges->valueRanges)
            buffer.push_back(&bindCovergroupExpr(*elem, context, type));
        expr->intersects = buffer.copy(comp);
    }

    return *expr;
}

void ConditionBinsSelectExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("target", target);
    if (!intersects.empty()) {
        serializer.startArray("intersects");
        for (auto item : intersects)
            serializer.serialize(*item);
        serializer.endArray();
    }
}

BinsSelectExpr& UnaryBinsSelectExpr::fromSyntax(const UnaryBinsSelectExprSyntax& syntax,
                                                const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);
    return *comp.emplace<UnaryBinsSelectExpr>(expr);
}

void UnaryBinsSelectExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("op", "negation"sv);
}

BinsSelectExpr& BinaryBinsSelectExpr::fromSyntax(const BinaryBinsSelectExprSyntax& syntax,
                                                 const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& left = bind(*syntax.left, context);
    auto& right = bind(*syntax.right, context);
    Op op = syntax.op.kind == TokenKind::DoubleAnd ? And : Or;
    return *comp.emplace<BinaryBinsSelectExpr>(left, right, op);
}

void BinaryBinsSelectExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left);
    serializer.write("right", right);
    serializer.write("op", op == And ? "and"sv : "or"sv);
}

BinsSelectExpr& SetExprBinsSelectExpr::fromSyntax(const SimpleBinsSelectExprSyntax& syntax,
                                                  const ASTContext& context) {
    auto& body = context.scope->asSymbol().as<CoverCrossBodySymbol>();
    SLANG_ASSERT(body.crossQueueType);

    auto parent = body.getParentScope();
    SLANG_ASSERT(parent);

    // If the syntax is a simple identifier that names our parent cross,
    // we're selecting the whole cross (which is otherwise not an expression).
    auto& comp = context.getCompilation();
    auto& cross = parent->asSymbol().as<CoverCrossSymbol>();
    if (syntax.expr->kind == SyntaxKind::IdentifierName &&
        syntax.expr->as<IdentifierNameSyntax>().identifier.valueText() == cross.name) {

        if (syntax.matchesClause)
            context.addDiag(diag::InvalidBinsMatches, syntax.matchesClause->sourceRange());

        return *comp.emplace<CrossIdBinsSelectExpr>();
    }

    const Expression* matches = nullptr;
    if (syntax.matchesClause) {
        matches =
            &bindCovergroupExpr(*syntax.matchesClause->pattern->as<ExpressionPatternSyntax>().expr,
                                context, nullptr, ASTFlags::AllowUnboundedLiteral);
        if (!matches->bad() && !matches->type->isUnbounded())
            context.requireIntegral(*matches);
    }

    auto& expr = Expression::bindRValue(*body.crossQueueType, *syntax.expr, {}, context);
    return *comp.emplace<SetExprBinsSelectExpr>(expr, matches);
}

void SetExprBinsSelectExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    if (matchesExpr)
        serializer.write("matchesExpr", *matchesExpr);
}

BinsSelectExpr& BinSelectWithFilterExpr::fromSyntax(const BinSelectWithFilterExprSyntax& syntax,
                                                    const ASTContext& context) {
    auto& comp = context.getCompilation();
    auto& expr = bind(*syntax.expr, context);

    // Create the iterator variables for all of the parent cross items
    // and then bind the filter expression.
    ASTContext iterCtx = context;

    auto& cross = context.scope->asSymbol().getParentScope()->asSymbol().as<CoverCrossSymbol>();
    for (auto target : cross.targets) {
        auto arrayType = comp.emplace<DynamicArrayType>(target->getType());
        auto it = comp.emplace<IteratorSymbol>(*context.scope, target->name, target->location,
                                               *arrayType, ""sv);
        it->nextTemp = std::exchange(iterCtx.firstTempVar, it);
    }

    auto& filter = bindCovergroupExpr(*syntax.filter, iterCtx);
    iterCtx.requireBooleanConvertible(filter);

    const Expression* matches = nullptr;
    if (syntax.matchesClause) {
        matches =
            &bindCovergroupExpr(*syntax.matchesClause->pattern->as<ExpressionPatternSyntax>().expr,
                                context, nullptr, ASTFlags::AllowUnboundedLiteral);
        if (!matches->bad() && !matches->type->isUnbounded())
            context.requireIntegral(*matches);
    }

    return *comp.emplace<BinSelectWithFilterExpr>(expr, filter, matches);
}

void BinSelectWithFilterExpr::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
    serializer.write("filter", filter);
    if (matchesExpr)
        serializer.write("matchesExpr", *matchesExpr);
}

} // namespace slang::ast

//------------------------------------------------------------------------------
// CompilationUnitSymbols.cpp
// Contains compilation unit-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/symbols/CompilationUnitSymbols.h"

#include "ParameterBuilder.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxTree.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

CompilationUnitSymbol::CompilationUnitSymbol(Compilation& compilation,
                                             const SourceLibrary& sourceLibrary) :
    Symbol(SymbolKind::CompilationUnit, "", SourceLocation()),
    Scope(compilation, this), sourceLibrary(sourceLibrary) {

    // Default the time scale to the compilation default. If it turns out
    // this scope has a time unit declaration it will overwrite the member.
    timeScale = compilation.getDefaultTimeScale();

    // All compilation units import the std package automatically.
    auto& stdPkg = compilation.getStdPackage();
    auto import = compilation.emplace<WildcardImportSymbol>(stdPkg.name,
                                                            SourceLocation::NoLocation);
    import->setPackage(stdPkg);
    addWildcardImport(*import);
}

void CompilationUnitSymbol::addMembers(const SyntaxNode& syntax) {
    if (syntax.kind == SyntaxKind::TimeUnitsDeclaration) {
        if (!timeScale)
            timeScale.emplace();

        SemanticFacts::populateTimeScale(*timeScale, *this, syntax.as<TimeUnitsDeclarationSyntax>(),
                                         unitsRange, precisionRange, !anyMembers);
    }
    else if (syntax.kind == SyntaxKind::CompilationUnit) {
        auto& cu = syntax.as<CompilationUnitSyntax>();
        if (!cu.members.empty()) {
            anyMembers = true;
            for (auto member : cu.members)
                Scope::addMembers(*member);
        }
    }
    else {
        anyMembers = true;
        Scope::addMembers(syntax);
    }
}

PackageSymbol::PackageSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                             const NetType& defaultNetType, VariableLifetime defaultLifetime) :
    Symbol(SymbolKind::Package, name, loc),
    Scope(compilation, this), defaultNetType(defaultNetType), defaultLifetime(defaultLifetime) {
}

PackageSymbol& PackageSymbol::fromSyntax(const Scope& scope, const ModuleDeclarationSyntax& syntax,
                                         const NetType& defaultNetType,
                                         std::optional<TimeScale> directiveTimeScale) {
    auto& comp = scope.getCompilation();
    auto lifetime = SemanticFacts::getVariableLifetime(syntax.header->lifetime);
    auto result = comp.emplace<PackageSymbol>(comp, syntax.header->name.valueText(),
                                              syntax.header->name.location(), defaultNetType,
                                              lifetime.value_or(VariableLifetime::Static));
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    bool first = true;
    std::optional<SourceRange> unitsRange;
    std::optional<SourceRange> precisionRange;
    SmallVector<const PackageImportItemSyntax*> exportDecls;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            if (!result->timeScale)
                result->timeScale.emplace();

            SemanticFacts::populateTimeScale(*result->timeScale, scope,
                                             member->as<TimeUnitsDeclarationSyntax>(), unitsRange,
                                             precisionRange, first);
            continue;
        }

        first = false;

        if (member->kind == SyntaxKind::PackageExportAllDeclaration) {
            result->hasExportAll = true;
        }
        else if (member->kind == SyntaxKind::PackageExportDeclaration) {
            for (auto item : member->as<PackageExportDeclarationSyntax>().items)
                exportDecls.push_back(item);
        }

        result->addMembers(*member);
    }

    result->exportDecls = exportDecls.copy(comp);

    SemanticFacts::populateTimeScale(result->timeScale, scope, directiveTimeScale, unitsRange,
                                     precisionRange);
    return *result;
}

const Symbol* PackageSymbol::findForImport(std::string_view lookupName) const {
    auto sym = find(lookupName);
    if (sym)
        return sym;

    if (!hasExportAll && exportDecls.empty())
        return nullptr;

    // We need to force-elaborate the entire package body because any
    // lookups that result in a wildcard import could add to our export list.
    auto& comp = getCompilation();
    if (!hasForceElaborated) {
        hasForceElaborated = true;
        comp.forceElaborate(*this);
    }

    return comp.findPackageExportCandidate(*this, lookupName);
}

void PackageSymbol::noteImport(const Symbol& symbol) const {
    // If we have an export directive for this symbol then add it to the list of export candidates.
    auto& comp = getCompilation();
    if (hasExportAll) {
        comp.notePackageExportCandidate(*this, symbol);
        return;
    }

    if (exportDecls.empty())
        return;

    const Symbol* packageParent;
    auto targetScope = symbol.getParentScope();
    while (true) {
        SLANG_ASSERT(targetScope);
        packageParent = &targetScope->asSymbol();
        if (packageParent->kind == SymbolKind::Package)
            break;

        targetScope = packageParent->getParentScope();
    }

    for (auto decl : exportDecls) {
        if (decl->package.valueText() != packageParent->name)
            continue;

        if (decl->item.kind == TokenKind::Star || decl->item.valueText() == symbol.name) {
            comp.notePackageExportCandidate(*this, symbol);
            return;
        }
    }
}

DefinitionSymbol::ParameterDecl::ParameterDecl(
    const Scope& scope, const ParameterDeclarationSyntax& syntax, const DeclaratorSyntax& decl,
    bool isLocal, bool isPort, std::span<const syntax::AttributeInstanceSyntax* const> attributes) :
    valueSyntax(&syntax),
    valueDecl(&decl), attributes(attributes), isTypeParam(false), isLocalParam(isLocal),
    isPortParam(isPort), hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.initializer) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

DefinitionSymbol::ParameterDecl::ParameterDecl(
    const Scope& scope, const TypeParameterDeclarationSyntax& syntax,
    const TypeAssignmentSyntax& decl, bool isLocal, bool isPort,
    std::span<const syntax::AttributeInstanceSyntax* const> attributes) :
    typeSyntax(&syntax),
    typeDecl(&decl), attributes(attributes), isTypeParam(true), isLocalParam(isLocal),
    isPortParam(isPort), hasSyntax(true) {

    name = decl.name.valueText();
    location = decl.name.location();

    if (!decl.assignment) {
        if (!isPort)
            scope.addDiag(diag::BodyParamNoInitializer, location);
        else if (isLocal)
            scope.addDiag(diag::LocalParamNoInitializer, location);
    }
}

DefinitionSymbol::ParameterDecl::ParameterDecl(std::string_view name, SourceLocation location,
                                               const Type& givenType, bool isLocal, bool isPort,
                                               const Expression* givenInitializer) :
    givenType(&givenType),
    givenInitializer(givenInitializer), name(name), location(location), isTypeParam(false),
    isLocalParam(isLocal), isPortParam(isPort), hasSyntax(false) {
    SLANG_ASSERT(givenInitializer || (isPort && !isLocal));
}

DefinitionSymbol::ParameterDecl::ParameterDecl(std::string_view name, SourceLocation location,
                                               bool isLocal, bool isPort, const Type* defaultType) :
    givenType(defaultType),
    name(name), location(location), isTypeParam(true), isLocalParam(isLocal), isPortParam(isPort),
    hasSyntax(false) {
    SLANG_ASSERT(givenType || (isPort && !isLocal));
}

bool DefinitionSymbol::ParameterDecl::hasDefault() const {
    if (hasSyntax) {
        if (isTypeParam)
            return typeDecl && typeDecl->assignment != nullptr;
        else
            return valueDecl && valueDecl->initializer != nullptr;
    }
    else {
        if (isTypeParam)
            return givenType != nullptr;
        else
            return givenInitializer != nullptr;
    }
}

static const SourceLibrary& getLibForDef(const Scope& scope, const SyntaxTree* syntaxTree) {
    if (syntaxTree) {
        if (auto lib = syntaxTree->getSourceLibrary())
            return *lib;
    }

    return scope.getCompilation().getDefaultLibrary();
}

DefinitionSymbol::DefinitionSymbol(const Scope& scope, LookupLocation lookupLocation,
                                   const ModuleDeclarationSyntax& syntax,
                                   const NetType& defaultNetType, UnconnectedDrive unconnectedDrive,
                                   std::optional<TimeScale> directiveTimeScale,
                                   const SyntaxTree* syntaxTree) :
    Symbol(SymbolKind::Definition, syntax.header->name.valueText(), syntax.header->name.location()),
    defaultNetType(defaultNetType), unconnectedDrive(unconnectedDrive), syntaxTree(syntaxTree),
    sourceLibrary(getLibForDef(scope, syntaxTree)) {

    // Extract and save various properties of the definition.
    setParent(scope, lookupLocation.getIndex());
    setSyntax(syntax);
    setAttributes(scope, syntax.attributes);

    definitionKind = SemanticFacts::getDefinitionKind(syntax.kind);
    defaultLifetime = SemanticFacts::getVariableLifetime(syntax.header->lifetime)
                          .value_or(VariableLifetime::Static);

    auto header = syntax.header.get();
    if (header->ports && header->ports->kind == SyntaxKind::WildcardPortList) {
        auto& comp = scope.getCompilation();
        auto externMod = comp.getExternDefinition(name, scope);
        if (!externMod || externMod->kind != SyntaxKind::ExternModuleDecl)
            scope.addDiag(diag::MissingExternWildcardPorts, header->ports->sourceRange()) << name;
        else
            header = externMod->as<ExternModuleDeclSyntax>().header;
    }

    portList = header->ports;
    hasNonAnsiPorts = portList && portList->kind == SyntaxKind::NonAnsiPortList;

    // Find all port parameters.
    bool hasPortParams = header->parameters != nullptr;
    if (hasPortParams)
        ParameterBuilder::createDecls(scope, *header->parameters, parameters);

    bool first = true;
    std::optional<SourceRange> unitsRange;
    std::optional<SourceRange> precisionRange;

    for (auto member : syntax.members) {
        if (member->kind == SyntaxKind::TimeUnitsDeclaration) {
            if (!timeScale)
                timeScale.emplace();

            SemanticFacts::populateTimeScale(*timeScale, scope,
                                             member->as<TimeUnitsDeclarationSyntax>(), unitsRange,
                                             precisionRange, first);
            continue;
        }

        first = false;
        if (member->kind == SyntaxKind::ModportDeclaration) {
            for (auto item : member->as<ModportDeclarationSyntax>().items)
                modports.emplace(item->name.valueText());
        }
        else if (member->kind == SyntaxKind::ParameterDeclarationStatement) {
            auto declaration = member->as<ParameterDeclarationStatementSyntax>().parameter;
            bool isLocal = hasPortParams ||
                           declaration->keyword.kind == TokenKind::LocalParamKeyword;

            ParameterBuilder::createDecls(scope, *declaration, isLocal, /* isPort */ false,
                                          member->attributes, parameters);
        }
    }

    SemanticFacts::populateTimeScale(timeScale, scope, directiveTimeScale, unitsRange,
                                     precisionRange);
}

std::string_view DefinitionSymbol::getKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "module"sv;
        case DefinitionKind::Interface:
            return "interface"sv;
        case DefinitionKind::Program:
            return "program"sv;
        default:
            SLANG_UNREACHABLE;
    }
}

std::string_view DefinitionSymbol::getArticleKindString() const {
    switch (definitionKind) {
        case DefinitionKind::Module:
            return "a module"sv;
        case DefinitionKind::Interface:
            return "an interface"sv;
        case DefinitionKind::Program:
            return "a program"sv;
        default:
            SLANG_UNREACHABLE;
    }
}

void DefinitionSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("defaultNetType", defaultNetType);
    serializer.write("definitionKind", toString(definitionKind));
    serializer.write("defaultLifetime", toString(defaultLifetime));
    serializer.write("unconnectedDrive", toString(unconnectedDrive));

    if (timeScale)
        serializer.write("timeScale", timeScale->toString());

    if (!sourceLibrary.isDefault)
        serializer.write("sourceLibrary", sourceLibrary.name);
}

ResolvedConfig::ResolvedConfig(const ConfigBlockSymbol& useConfig,
                               const InstanceSymbol& rootInstance) :
    useConfig(useConfig),
    rootInstance(rootInstance), liblist(useConfig.getDefaultLiblist()) {
}

ConfigBlockSymbol& ConfigBlockSymbol::fromSyntax(const Scope& scope,
                                                 const ConfigDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.allocConfigBlock(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    for (auto param : syntax.localparams)
        result->addMembers(*param);

    return *result;
}

void ConfigBlockSymbol::resolve() const {
    SLANG_ASSERT(!resolved);
    resolved = true;

    auto scope = getParentScope();
    SLANG_ASSERT(getSyntax() && scope);

    auto& comp = scope->getCompilation();
    auto& syntax = getSyntax()->as<ConfigDeclarationSyntax>();

    SmallMap<std::string_view, size_t, 2> topCellNames;
    SmallVector<TopCell> topCellsBuf;
    for (auto cellId : syntax.topCells) {
        auto cellName = cellId->cell.valueText();
        if (!cellName.empty()) {
            auto def = comp.getDefinition(*this, cellName, cellId->library.valueText(),
                                          cellId->sourceRange());
            if (!def)
                continue;

            auto [it, inserted] = topCellNames.emplace(cellName, topCellsBuf.size());
            if (inserted)
                topCellsBuf.emplace_back(*def);
            else
                scope->addDiag(diag::ConfigDupTop, cellId->cell.range()) << cellName;
        }
    }

    auto buildLiblist = [&](const ConfigLiblistSyntax& cll) {
        SmallVector<const SourceLibrary*> buf;
        for (auto token : cll.libraries) {
            if (auto name = token.valueText(); !name.empty()) {
                if (auto lib = comp.getSourceLibrary(name))
                    buf.push_back(lib);
                else
                    scope->addDiag(diag::WarnUnknownLibrary, token.range()) << name;
            }
        }
        return buf.copy(comp);
    };

    auto buildRule = [&](const ConfigRuleClauseSyntax& rule) {
        ConfigRule result;
        result.sourceRange = rule.parent->sourceRange();
        if (rule.kind == SyntaxKind::ConfigUseClause) {
            auto& cuc = rule.as<ConfigUseClauseSyntax>();
            result.paramOverrides = cuc.paramAssignments;
            if (cuc.name && !cuc.name->cell.valueText().empty()) {
                result.useCell = ConfigCellId(cuc.name->library.valueText(),
                                              cuc.name->cell.valueText(), cuc.name->sourceRange());
                if (cuc.config)
                    result.useCell.targetConfig = true;
            }
        }
        else {
            result.liblist = buildLiblist(rule.as<ConfigLiblistSyntax>());
        }
        return result;
    };

    auto mergeRules = [&](ConfigRule& curRule, const ConfigRule& newRule, auto&& nameGetter) {
        if ((bool(newRule.paramOverrides) && bool(curRule.paramOverrides)) ||
            (newRule.liblist.has_value() && curRule.liblist.has_value()) ||
            (!newRule.useCell.name.empty() && !curRule.useCell.name.empty())) {

            auto& diag = scope->addDiag(diag::DupConfigRule, newRule.sourceRange) << nameGetter();
            diag.addNote(diag::NotePreviousDefinition, curRule.sourceRange);
        }
        else {
            if (newRule.paramOverrides)
                curRule.paramOverrides = newRule.paramOverrides;
            if (newRule.liblist)
                curRule.liblist = newRule.liblist;
            if (!newRule.useCell.name.empty())
                curRule.useCell = newRule.useCell;
        }
    };

    for (auto ruleSyntax : syntax.rules) {
        switch (ruleSyntax->kind) {
            case SyntaxKind::DefaultConfigRule:
                defaultLiblist = buildLiblist(*ruleSyntax->as<DefaultConfigRuleSyntax>().liblist);
                break;
            case SyntaxKind::CellConfigRule: {
                auto& ccr = ruleSyntax->as<CellConfigRuleSyntax>();
                auto cellName = ccr.name->cell.valueText();
                if (cellName.empty())
                    break;

                CellOverride co;
                if (auto libName = ccr.name->library.valueText(); !libName.empty()) {
                    co.specificLib = comp.getSourceLibrary(libName);
                    if (!co.specificLib) {
                        scope->addDiag(diag::WarnUnknownLibrary, ccr.name->library.range())
                            << libName;
                        break;
                    }
                }

                co.rule = buildRule(*ccr.ruleClause);

                auto& overrides = cellOverrides[cellName];
                auto it = std::ranges::find_if(overrides, [&](auto& item) {
                    return item.specificLib == co.specificLib;
                });

                if (it != overrides.end()) {
                    mergeRules(it->rule, co.rule, [&] {
                        std::string name = "cell '";
                        if (co.specificLib) {
                            name += ccr.name->library.valueText();
                            name.push_back('.');
                        }
                        name += cellName;
                        name.push_back('\'');
                        return name;
                    });
                }
                else {
                    overrides.push_back(co);
                }
                break;
            }
            case SyntaxKind::InstanceConfigRule: {
                auto& icr = ruleSyntax->as<InstanceConfigRuleSyntax>();
                const auto topName = icr.topModule.valueText();
                if (topName.empty())
                    break;

                if (!topCellNames.contains(topName)) {
                    scope->addDiag(diag::ConfigInstanceWrongTop, icr.topModule.range());
                    break;
                }

                bool bad = false;
                auto node = &instanceOverrides[topName];
                for (auto& part : icr.instanceNames) {
                    auto partName = part->name.valueText();
                    bad |= partName.empty();
                    node = &node->childNodes[partName];
                }

                if (bad)
                    break;

                auto rule = buildRule(*icr.ruleClause);
                if (!node->rule) {
                    // No rule here yet; copy into our allocator and save it.
                    node->rule = comp.emplace<ConfigRule>(rule);
                }
                else {
                    // Merge the two rules, or warn if we cannot.
                    mergeRules(*node->rule, rule, [&] {
                        std::string name = "instance '";
                        name += topName;
                        for (auto& part : icr.instanceNames) {
                            name.push_back('.');
                            name += part->name.valueText();
                        }
                        name.push_back('\'');
                        return name;
                    });
                }
                break;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }

    // Check if any overrides should apply to the root instances.
    // TODO: check validity of overrides here as applied to a root instance
    for (auto& [cellName, instOverride] : instanceOverrides) {
        if (instOverride.rule) {
            auto it = topCellNames.find(cellName);
            SLANG_ASSERT(it != topCellNames.end());
            topCellsBuf[it->second].rule = instOverride.rule;
        }
    }

    for (auto& topCell : topCellsBuf) {
        // If we already set a rule for this cell via an instance
        // override we don't need a less specific cell override.
        if (topCell.rule)
            continue;

        if (auto it = cellOverrides.find(topCell.definition.name); it != cellOverrides.end()) {
            CellOverride* defaultOverride = nullptr;
            for (auto& co : it->second) {
                if (!co.specificLib) {
                    defaultOverride = &co;
                }
                else if (co.specificLib == &topCell.definition.sourceLibrary) {
                    topCell.rule = &co.rule;
                    break;
                }
            }

            if (!topCell.rule && defaultOverride)
                topCell.rule = &defaultOverride->rule;
        }
    }

    topCells = topCellsBuf.copy(comp);
}

void ConfigBlockSymbol::serializeTo(ASTSerializer&) const {
    // TODO:
}

} // namespace slang::ast

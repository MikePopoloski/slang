// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <fmt/core.h>

#include "slang/ast/ASTVisitor.h"
#include "slang/parsing/ParserMetadata.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxVisitor.h"

class SemanticModel {
public:
    explicit SemanticModel(Compilation& compilation) : compilation(compilation) {}

    const Symbol* getDeclaredSymbol(const syntax::SyntaxNode& syntax) {
        // If we've already cached this node, return that.
        if (auto it = symbolCache.find(&syntax); it != symbolCache.end())
            return it->second;

        // If we hit the top of the syntax tree, look in the compilation for the correct symbol.
        if (syntax.kind == SyntaxKind::CompilationUnit) {
            auto result = compilation.getCompilationUnit(syntax.as<CompilationUnitSyntax>());
            if (result)
                symbolCache[&syntax] = result;
            return result;
        }
        else if (syntax.kind == SyntaxKind::ModuleDeclaration ||
                 syntax.kind == SyntaxKind::InterfaceDeclaration ||
                 syntax.kind == SyntaxKind::ProgramDeclaration) {
            auto [parentScope, parentSym] = getParent(syntax);
            if (!parentScope)
                parentScope = &compilation.getRoot();

            auto def = compilation.getDefinition(*parentScope,
                                                 syntax.as<ModuleDeclarationSyntax>());
            if (!def)
                return nullptr;

            // There is no symbol to use here so create a placeholder instance.
            auto result = &InstanceSymbol::createDefault(compilation, *def);
            symbolCache[&syntax] = result;
            return result;
        }

        // Otherwise try to find the parent symbol first.
        auto [parentScope, parentSym] = getParent(syntax);
        if (!parentSym)
            return nullptr;

        // If this is a type alias, unwrap its target type to look at the syntax node.
        if (parentSym->kind == SymbolKind::TypeAlias) {
            auto& target = parentSym->as<TypeAliasType>().targetType.getType();
            if (target.getSyntax() == &syntax) {
                symbolCache.emplace(&syntax, &target);
                return &target;
            }
            return nullptr;
        }

        if (!parentScope)
            return nullptr;

        // Search among the parent's children to see if we can find ourself.
        for (auto& child : parentScope->members()) {
            if (child.getSyntax() == &syntax) {
                // We found ourselves, hurray.
                symbolCache.emplace(&syntax, &child);
                return &child;
            }
        }

        return nullptr;
    }

    const CompilationUnitSymbol* getDeclaredSymbol(const CompilationUnitSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<CompilationUnitSymbol>() : nullptr;
    }

    const InstanceSymbol* getDeclaredSymbol(const HierarchyInstantiationSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<InstanceSymbol>() : nullptr;
    }

    const StatementBlockSymbol* getDeclaredSymbol(const BlockStatementSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<StatementBlockSymbol>() : nullptr;
    }

    const ProceduralBlockSymbol* getDeclaredSymbol(const ProceduralBlockSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<ProceduralBlockSymbol>() : nullptr;
    }

    const GenerateBlockSymbol* getDeclaredSymbol(const IfGenerateSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<GenerateBlockSymbol>() : nullptr;
    }

    const GenerateBlockArraySymbol* getDeclaredSymbol(const LoopGenerateSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<GenerateBlockArraySymbol>() : nullptr;
    }

    const SubroutineSymbol* getDeclaredSymbol(const FunctionDeclarationSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<SubroutineSymbol>() : nullptr;
    }

    const EnumType* getDeclaredSymbol(const EnumTypeSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<EnumType>() : nullptr;
    }

    const TypeAliasType* getDeclaredSymbol(const TypedefDeclarationSyntax& syntax) {
        auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
        return result ? &result->as<TypeAliasType>() : nullptr;
    }

private:
    std::pair<const Scope*, const Symbol*> getParent(const SyntaxNode& syntax) {
        auto parent = syntax.parent ? getDeclaredSymbol(*syntax.parent) : nullptr;
        if (!parent)
            return {nullptr, nullptr};

        if (parent->kind == SymbolKind::Instance)
            parent = &parent->as<InstanceSymbol>().body;
        else if (!parent->isScope())
            return {nullptr, parent};

        return {&parent->as<Scope>(), parent};
    }

    Compilation& compilation;
    flat_hash_map<const syntax::SyntaxNode*, const Symbol*> symbolCache;
};

template<typename T>
class RewriterBase : public SyntaxRewriter<T> {
public:
    FunctionPortSyntax& makeArg(std::string_view name) {
        return this->factory.functionPort(nullptr, {}, {}, {}, {}, nullptr,
                                          this->factory.declarator(this->makeId(name), nullptr,
                                                                   nullptr));
    }
};

class TestRewriter : public RewriterBase<TestRewriter> {
public:
    Compilation compilation;
    SemanticModel model;

    TestRewriter(const std::shared_ptr<SyntaxTree>& tree) : model(compilation) {
        compilation.addSyntaxTree(tree);
    }

    void handle(const TypedefDeclarationSyntax& decl) {
        if (decl.type->kind != SyntaxKind::EnumType)
            return;

        // Create a new localparam hardcoded with the number of entries in the enum.
        auto type = model.getDeclaredSymbol(decl.type->as<EnumTypeSyntax>());
        REQUIRE(type);

        size_t count = std::ranges::distance(type->as<EnumType>().members());
        auto& newNode = parse(
            fmt::format("\n    localparam int {}__count = {};", decl.name.valueText(), count));
        insertAfter(decl, newNode);
    }

    void handle(const FunctionDeclarationSyntax& decl) {
        auto portList = decl.prototype->portList;
        if (!portList)
            return;

        insertAtFront(portList->ports, makeArg("argA"), makeComma());
        insertAtBack(portList->ports, makeArg("argZ"), makeComma());
    }
};

TEST_CASE("Basic rewriting") {
    auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;

    function void foo(int i, output r);
    endfunction
endmodule
)");

    tree = TestRewriter(tree).transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
    localparam int test_t__count = 3;

    function void foo(argA,int i, output r,argZ);
    endfunction
endmodule
)");
}

TEST_CASE("Rewriting around macros") {
    auto tree = SyntaxTree::fromText(R"(
`define ENUM_MACRO(asdf) \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } asdf;

module M;
    `ENUM_MACRO(test_t)
endmodule
)");

    tree = TestRewriter(tree).transform(tree);

    CHECK(SyntaxPrinter::printFile(*tree) == R"(
`define ENUM_MACRO(asdf) \
    typedef enum int {\
        FOO = 1,\
        BAR = 2,\
        BAZ = 3\
    } asdf;

module M;
    `ENUM_MACRO(test_t)
    localparam int test_t__count = 3;
endmodule
)");
}

TEST_CASE("Remove node from cloned object") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter P = 8)();
    reg tmp;
endmodule
)");
    struct RemoveWriter : public SyntaxRewriter<RemoveWriter> {
        void handle(const ParameterPortListSyntax& decl) { remove(decl); }
    };
    tree = RemoveWriter().transform(tree);
    CHECK(SyntaxPrinter::printFile(*tree) == R"(
module m();
    reg tmp;
endmodule
)");
}

TEST_CASE("Remove node from comma-separated list") {
    auto tree = SyntaxTree::fromText(R"(
    // normal case
    function void foo1(int a, int b, int c, int d, int e);
    endfunction
    // case with trailing comma
    function void foo2(int a, int b, int c, int d, int e,);
    endfunction
    // case with duplicated comma
    function void foo3(int a, int b,, int c, int d, int e);
    endfunction
)");
    struct RemoveWriter : public SyntaxRewriter<RemoveWriter> {
        void handle(const FunctionPortBaseSyntax& port) {
            std::string str = port.toString();
            str.erase(0, str.find_first_not_of(' ')); // trim left whitespace
            if (str == "int a" or str == "int c" or str == "int e")
                remove(port);
        }
    };
    tree = RemoveWriter().transform(tree);
    CHECK(SyntaxPrinter::printFile(*tree) == R"(
    // normal case
    function void foo1( int b, int d);
    endfunction
    // case with trailing comma
    function void foo2( int b, int d,);
    endfunction
    // case with duplicated comma
    function void foo3( int b,, int d);
    endfunction
)");
}
TEST_CASE("Advanced rewriting") {
    SECTION("Insert multiple newNodes surrounding oldNodes") {
        class MultipleRewriter : public RewriterBase<MultipleRewriter> {
        public:
            Compilation compilation;
            SemanticModel model;

            MultipleRewriter(const std::shared_ptr<SyntaxTree>& tree) : model(compilation) {
                compilation.addSyntaxTree(tree);
            }

            void handle(const TypedefDeclarationSyntax& decl) {
                if (decl.type->kind != SyntaxKind::EnumType)
                    return;

                // Create a new localparam hardcoded with the number of entries in the enum.
                auto type = model.getDeclaredSymbol(decl.type->as<EnumTypeSyntax>());
                REQUIRE(type);

                size_t count = std::ranges::distance(type->as<EnumType>().members());
                auto& newNode1 = parse(fmt::format("\n    localparam int {}__count1 = {};",
                                                   decl.name.valueText(), count));
                insertBefore(decl, newNode1);
                auto& newNode2 = parse(fmt::format("\n    localparam int {}__count2 = {};",
                                                   decl.name.valueText(), count));
                insertBefore(decl, newNode2);
                auto& newNode3 = parse(fmt::format("\n    localparam int {}__count3 = {};",
                                                   decl.name.valueText(), count));
                insertAfter(decl, newNode3);
                auto& newNode4 = parse(fmt::format("\n    localparam int {}__count4 = {};",
                                                   decl.name.valueText(), count));
                insertAfter(decl, newNode4);
            }

            void handle(const FunctionDeclarationSyntax& decl) {
                auto portList = decl.prototype->portList;
                if (!portList)
                    return;

                insertAtFront(portList->ports, makeArg("argA"), makeComma());
                insertAtBack(portList->ports, makeArg("argZ"), makeComma());
            }
        };

        auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;

    function void foo(int i, output r);
    endfunction
endmodule
)");

        tree = MultipleRewriter(tree).transform(tree);

        CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    localparam int test_t__count1 = 3;
    localparam int test_t__count2 = 3;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;
    localparam int test_t__count3 = 3;
    localparam int test_t__count4 = 3;

    function void foo(argA,int i, output r,argZ);
    endfunction
endmodule
)");
    }
    SECTION("Combine insert and replace operation on oldNodes") {
        class InterleavedRewriter : public RewriterBase<InterleavedRewriter> {
        public:
            Compilation compilation;
            SemanticModel model;

            InterleavedRewriter(const std::shared_ptr<SyntaxTree>& tree) : model(compilation) {
                compilation.addSyntaxTree(tree);
            }

            void handle(const TypedefDeclarationSyntax& decl) {
                if (decl.type->kind != SyntaxKind::EnumType)
                    return;

                // Create a new localparam hardcoded with the number of entries in the enum.
                auto type = model.getDeclaredSymbol(decl.type->as<EnumTypeSyntax>());
                REQUIRE(type);

                size_t count = std::ranges::distance(type->as<EnumType>().members());
                auto& newNode1 = parse(fmt::format("\n    localparam int {}__count1 = {};",
                                                   decl.name.valueText(), count));
                insertBefore(decl, newNode1);
                auto& newNode2 = parse(fmt::format("\n    localparam int {}__count2 = {};",
                                                   decl.name.valueText(), count));
                replace(decl, newNode2);
                auto& newNode3 = parse(fmt::format("\n    localparam int {}__count3 = {};",
                                                   decl.name.valueText(), count));
                insertAfter(decl, newNode3);
            }

            void handle(const FunctionDeclarationSyntax& decl) {
                auto portList = decl.prototype->portList;
                if (!portList)
                    return;

                insertAtFront(portList->ports, makeArg("argA"), makeComma());
                insertAtBack(portList->ports, makeArg("argZ"), makeComma());
            }
        };

        auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;

    function void foo(int i, output r);
    endfunction
endmodule
)");

        tree = InterleavedRewriter(tree).transform(tree);
        CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    localparam int test_t__count1 = 3;
    localparam int test_t__count2 = 3;
    localparam int test_t__count3 = 3;

    function void foo(argA,int i, output r,argZ);
    endfunction
endmodule
)");
    }
    SECTION("Combine insert and remove operation on oldNodes") {
        class InterleavedRewriter : public RewriterBase<InterleavedRewriter> {
        public:
            Compilation compilation;
            SemanticModel model;

            InterleavedRewriter(const std::shared_ptr<SyntaxTree>& tree) : model(compilation) {
                compilation.addSyntaxTree(tree);
            }

            void handle(const TypedefDeclarationSyntax& decl) {
                if (decl.type->kind != SyntaxKind::EnumType)
                    return;

                // Create a new localparam hardcoded with the number of entries in the enum.
                auto type = model.getDeclaredSymbol(decl.type->as<EnumTypeSyntax>());
                REQUIRE(type);

                size_t count = std::ranges::distance(type->as<EnumType>().members());
                auto& newNode1 = parse(fmt::format("\n    localparam int {}__count1 = {};",
                                                   decl.name.valueText(), count));
                insertBefore(decl, newNode1);
                auto& newNode2 = parse(fmt::format("\n    localparam int {}__count2 = {};",
                                                   decl.name.valueText(), count));
                insertAfter(decl, newNode2);
                remove(decl);
            }

            void handle(const FunctionDeclarationSyntax& decl) {
                auto portList = decl.prototype->portList;
                if (!portList)
                    return;

                insertAtFront(portList->ports, makeArg("argA"), makeComma());
                insertAtBack(portList->ports, makeArg("argZ"), makeComma());
            }
        };

        auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1, BAR = 2, BAZ = 3 } test_t;

    function void foo(int i, output r);
    endfunction
endmodule
)");

        tree = InterleavedRewriter(tree).transform(tree);
        CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    localparam int test_t__count1 = 3;
    localparam int test_t__count2 = 3;

    function void foo(argA,int i, output r,argZ);
    endfunction
endmodule
)");
    }

    SECTION("Reuse same rewriter object") {
        struct FirstTypedefRemover : public SyntaxRewriter<FirstTypedefRemover> {
            int index;
            void handle(const TypedefDeclarationSyntax& decl) {
                if (index++ == 0)
                    remove(decl);
            }
            std::shared_ptr<SyntaxTree> transform(const std::shared_ptr<SyntaxTree>& tree) {
                index = 0;
                return SyntaxRewriter<FirstTypedefRemover>::transform(tree);
            }
        };
        auto tree = SyntaxTree::fromText(R"(
module M;
    typedef enum int { FOO = 1 } test_t_1;
    typedef enum int { BAR = 2 } test_t_2;
    typedef enum int { BAZ = 3 } test_t_3;
endmodule
)");

        FirstTypedefRemover rewriter;
        tree = rewriter.transform(tree);
        tree = rewriter.transform(tree);

        CHECK(SyntaxPrinter::printFile(*tree) == R"(
module M;
    typedef enum int { BAZ = 3 } test_t_3;
endmodule
)");
    }
}

TEST_CASE("Test AST visiting") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    initial begin
        if (1) begin
            int i = {1 + 2, 5 + 6};
        end
    end
    int j = 3 + 4;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Visit the whole tree and count the binary expressions.
    int count = 0;
    compilation.getRoot().visit(makeVisitor([&](auto& v, const BinaryExpression& expr) {
        count++;
        v.visitDefault(expr);
    }));
    CHECK(count == 3);
}

struct Visitor : public ASTVisitor<Visitor, true, true> {
    int count = 0;
    template<typename T>
    void handle(const T& t) {
        if constexpr (std::is_base_of_v<Statement, T>) {
            count++;
        }
        visitDefault(t);
    }
};

TEST_CASE("Test single counting of statements") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int j;
    initial begin : asdf
        j = j + 3;
        if (1) begin : baz
            static int i;
            i = i + 2;
            if (1) begin : boz
                i = i + 4;
            end
        end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    // Visit the whole tree and count the statements.
    Visitor visitor;
    compilation.getRoot().visit(visitor);
    CHECK(visitor.count == 11);
}

TEST_CASE("Clone and DeepClone") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    reg tmp;
endmodule
)");

    SECTION("Shallow Clone") {
        class CloneRewriter : public SyntaxRewriter<CloneRewriter> {
        public:
            void handle(const DataDeclarationSyntax& syntax) {
                auto op = [this, &syntax](std::string_view str) {
                    auto cloned = clone(syntax, alloc);
                    cloned->declarators[0]->name = cloned->declarators[0]->name.withRawText(alloc,
                                                                                            str);
                    insertAfter(syntax, *cloned);
                };
                op("tmp1");
                op("tmp2");
                op("tmp3");
            }
        };

        auto newTree = CloneRewriter().transform(tree);
        CHECK(SyntaxPrinter::printFile(*newTree) == R"(
module m;
    reg tmp3;
    reg tmp3;
    reg tmp3;
    reg tmp3;
endmodule
)");
    }

    SECTION("Deep Clone") {
        class CloneRewriter : public SyntaxRewriter<CloneRewriter> {
        public:
            void handle(const DataDeclarationSyntax& syntax) {
                auto op = [this, &syntax](std::string_view str) {
                    auto cloned = deepClone(syntax, alloc);
                    cloned->declarators[0]->name = cloned->declarators[0]->name.withRawText(alloc,
                                                                                            str);
                    insertAfter(syntax, *cloned);
                };
                op("tmp1");
                op("tmp2");
                op("tmp3");
            }
        };

        tree = CloneRewriter().transform(tree);
        CHECK(SyntaxPrinter::printFile(*tree) == R"(
module m;
    reg tmp;
    reg tmp1;
    reg tmp2;
    reg tmp3;
endmodule
)");
    }

    SECTION("Deep Clone With different object life cycle") {
        auto tree = SyntaxTree::fromText(R"(module m; reg tmp; endmodule)");
        class CloneRewriter : public SyntaxVisitor<CloneRewriter> {
            std::shared_ptr<SyntaxTree>& tree;

        public:
            CloneRewriter(std::shared_ptr<SyntaxTree>& tree) : tree(tree) {}
            void handle(const ModuleDeclarationSyntax& decl) {
                BumpAllocator newAlloc;
                auto newModule = slang::syntax::deepClone(decl, newAlloc);
                tree = std::make_shared<SyntaxTree>(newModule, tree->sourceManager(),
                                                    std::move(newAlloc), nullptr);
            }
        };
        CloneRewriter visitor(tree);
        tree->root().visit(visitor);
        CHECK(SyntaxPrinter::printFile(*tree) == R"(module m; reg tmp; endmodule)");
    }
}

TEST_CASE("Syntax rewriting with metadata updates") {
    auto tree = SyntaxTree::fromFileInMemory(R"(
`default_nettype none
`unconnected_drive pull0
`timescale 1ns/1ps
`define FOO

module m;
    module n;
    endmodule
    reg tmp;
    n n();
    if (1) begin end
endmodule

module top;
    import bar::*;
    FooBar fooBar();
    defparam a = 1;
    bind A: Ainst Abind Abind_inst();

    initial a::b = 1;
endmodule

class C; endclass

`nounconnected_drive
`resetall
)",
                                             SyntaxTree::getDefaultSourceManager());

    CHECK(tree->diagnostics().empty());

    class ModuleChanger : public SyntaxRewriter<ModuleChanger> {
    public:
        void handle(const ModuleDeclarationSyntax& syntax) {
            if (syntax.header->name.valueText() == "m") {
                auto newMod = clone(syntax, alloc);
                newMod->header->name = makeId("FooBar", SingleSpace);
                replace(syntax, *newMod);
            }
        }
    };

    auto newTree = ModuleChanger().transform(tree);
    CHECK(SyntaxPrinter::printFile(*newTree) == R"(
`default_nettype none
`unconnected_drive pull0
`timescale 1ns/1ps
`define FOO

module FooBar;
    module n;
    endmodule
    reg tmp;
    n n();
    if (1) begin end
endmodule

module top;
    import bar::*;
    FooBar fooBar();
    defparam a = 1;
    bind A: Ainst Abind Abind_inst();

    initial a::b = 1;
endmodule

class C; endclass

`nounconnected_drive
`resetall
)");

    auto& meta = tree->getMetadata();
    CHECK(meta.nodeMap.size() == 3);

    for (auto& [key, node] : meta.nodeMap) {
        if (key->as<ModuleDeclarationSyntax>().header->name.valueText() == "FooBar") {
            CHECK(node.timeScale->base.unit == TimeUnit::Nanoseconds);
            CHECK(node.unconnectedDrive == TokenKind::Pull0Keyword);
        }
    }
}

TEST_CASE("Visit all file") {
    // Load a file containing all the SystemVerilog constructs and visit them
    // just to get coverage of all the visitor methods.
    fs::path path = findTestDir();
    path /= "../../regression/all.sv";
    auto tree = SyntaxTree::fromFile(path.string());
    REQUIRE(tree);

    Compilation compilation;
    compilation.addSyntaxTree(*tree);

    int count = 0;
    compilation.getRoot().visit(makeVisitor([&](auto& v, auto& elem) {
        count++;
        v.visitDefault(elem);
    }));

    CHECK(count == 1615);
}

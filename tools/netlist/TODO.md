To dos
======

- Bug report:

module m;
  logic [7:4] [3:2] foo;
  always_comb begin
    foo[0] = 0;
  end
endmodule

  Assertion 'range.left >= 0 && range.right >= 0' failed
    in file /home/jamie/slang/source/ast/symbols/ValueSymbol.cpp, line 436
    function: static std::optional<std::pair<uint32_t, uint32_t>> slang::ast::
  ValueDriver::getBounds(const Expression &, EvalContext &, const Type &)

- Support for more procedural statements, the full list is:

    InvalidStatement
    EmptyStatement
    StatementList
    BlockStatement
    ReturnStatement
    BreakStatement
    ContinueStatement
    DisableStatement
    VariableDeclStatement
    ConditionalStatement
    CaseStatement
    PatternCaseStatement
    ForLoopStatement
    RepeatLoopStatement
    ForeachLoopStatement
    WhileLoopStatement
    DoWhileLoopStatement
    ForeverLoopStatement
    ExpressionStatement
    TimedStatement
    ImmediateAssertionStatement
    ConcurrentAssertionStatement
    DisableForkStatement
    WaitStatement
    WaitForkStatement
    WaitOrderStatement
    EventTriggerStatement
    ProceduralAssignStatement
    ProceduralDeassignStatement
    RandCaseStatement
    RandSequenceStatement
    ProceduralCheckerStatement

- In SplitVariables, handle:
  * Unions, where they cause access cannot to no longer be tracked through a
    heirarchy of types. Instead access must be resolved on the bit level (bit blasted).
  * Variable positions in element or range selects [x:y].
    Note that in [x+:y] y must be a constant.
    Also handle [x-:y].

- Optimise lookups of nodes in the netlist by adding tables for variable
  declarations, variable references, ports etc.

- Dumping of a dot file outputs random characters at the end.
- Reporting of variables in the netlist (by type, matching patterns).
- Infer sequential elements in the netlist (ie non-blocking assignment and
  sensitive to a clock edge).
- Constrain paths to start on particular node types (port, register, net etc).
- Support restricting paths to stop at sequential elements.
- Support paths passing through particular nodes.
- Support paths avoiding particular nodes.
- Support reporting of paths fanning into or out of a particular node.
- Provide Python bindings.

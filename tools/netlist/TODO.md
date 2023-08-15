To dos
======

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
  * Nested range selections, eg `x[3:0][2:0][1:0]` has a dependency with
    `x[0]`, so effectively multiple ranges should be flattened eg to `[1:0]`.
  * Unions, where they cause access cannot to no longer be tracked through a
    heirarchy of types. Instead access must be resolved on the bit level (bit blasted).
  * Variable positions in element or range selects. Note that in [x+:y] y must be a
    constant.

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

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

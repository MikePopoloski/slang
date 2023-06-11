# ~~~
# SPDX-FileCopyrightText: Michael Popoloski
# SPDX-License-Identifier: MIT
# ~~~

target_sources(
  slang_slang
  PRIVATE builtins/ArrayMethods.cpp
          builtins/ConversionFuncs.cpp
          builtins/CoverageFuncs.cpp
          builtins/EnumMethods.cpp
          builtins/GateTypes.cpp
          builtins/MathFuncs.cpp
          builtins/MiscSystemFuncs.cpp
          builtins/NonConstFuncs.cpp
          builtins/QueryFuncs.cpp
          builtins/StdPackage.cpp
          builtins/StringMethods.cpp
          builtins/SystemTasks.cpp
          expressions/AssertionExpr.cpp
          expressions/AssignmentExpressions.cpp
          expressions/CallExpression.cpp
          expressions/LiteralExpressions.cpp
          expressions/MiscExpressions.cpp
          expressions/OperatorExpressions.cpp
          expressions/SelectExpressions.cpp
          symbols/AttributeSymbol.cpp
          symbols/BlockSymbols.cpp
          symbols/ClassSymbols.cpp
          symbols/CompilationUnitSymbols.cpp
          symbols/CoverSymbols.cpp
          symbols/InstanceSymbols.cpp
          symbols/MemberSymbols.cpp
          symbols/ParameterBuilder.cpp
          symbols/ParameterSymbols.cpp
          symbols/PortSymbols.cpp
          symbols/SpecifySymbols.cpp
          symbols/SubroutineSymbols.cpp
          symbols/SymbolBuilders.cpp
          symbols/ValueSymbol.cpp
          symbols/VariableSymbols.cpp
          types/AllTypes.cpp
          types/DeclaredType.cpp
          types/NetType.cpp
          types/TypePrinter.cpp
          types/Type.cpp
          ASTContext.cpp
          ASTSerializer.cpp
          Bitstream.cpp
          Compilation.cpp
          Constraints.cpp
          Definition.cpp
          EvalContext.cpp
          Expression.cpp
          FmtHelpers.cpp
          InstancePath.cpp
          Lookup.cpp
          LValue.cpp
          Patterns.cpp
          Scope.cpp
          ScriptSession.cpp
          SemanticFacts.cpp
          SemanticModel.cpp
          Statements.cpp
          Symbol.cpp
          SystemSubroutine.cpp
          TimingControl.cpp)

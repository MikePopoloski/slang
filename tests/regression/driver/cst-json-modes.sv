// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Exercises slang::syntax::CSTSerializer in every CSTJsonMode so that the
// mode-specific token/trivia serialization branches are covered.
//
// The SystemVerilog source lives in a separate fixture so that the marker
// strings echoed below (used to anchor the CHECK regions) never appear in the
// serialized output. The fixture's stray trailing token is a parse error, hence
// the trailing "|| true" on each command.

// RUN: echo CST-MODE-full && %slang --cst-json - --cst-json-mode full --parse-only %data/cst_serializer_modes.sv || true
// RUN: echo CST-MODE-no-whitespace && %slang --cst-json - --cst-json-mode no-whitespace --parse-only %data/cst_serializer_modes.sv || true
// RUN: echo CST-MODE-simple-trivia && %slang --cst-json - --cst-json-mode simple-trivia --parse-only %data/cst_serializer_modes.sv || true
// RUN: echo CST-MODE-no-trivia && %slang --cst-json - --cst-json-mode no-trivia --parse-only %data/cst_serializer_modes.sv || true
// RUN: echo CST-MODE-simple-tokens && %slang --cst-json - --cst-json-mode simple-tokens --parse-only %data/cst_serializer_modes.sv || true

// "full" mode keeps every trivia kind verbatim, including whitespace, the
// disabled `ifdef text, comments, directives and skipped tokens.
// CHECK-LABEL: CST-MODE-full
// CHECK-DAG: "kind": "Whitespace"
// CHECK-DAG: "kind": "DisabledText"
// CHECK-DAG: "kind": "Directive"
// CHECK-DAG: "kind": "LineComment"
// CHECK-DAG: "kind": "BlockComment"
// CHECK-DAG: "kind": "SkippedTokens"

// "no-whitespace" mode drops Whitespace/EndOfLine (and whitespace-only
// DisabledText) trivia but preserves comments, directives and skipped tokens.
// CHECK-LABEL: CST-MODE-no-whitespace
// CHECK-DAG: "kind": "Directive"
// CHECK-DAG: "kind": "LineComment"
// CHECK-DAG: "kind": "BlockComment"
// CHECK-DAG: "kind": "SkippedTokens"
// CHECK-NOT: "kind": "Whitespace"
// CHECK-NOT: "kind": "DisabledText"

// "simple-trivia" mode emits the trivia of each token as a single concatenated
// string value instead of an array of structured trivia objects.
// CHECK-LABEL: CST-MODE-simple-trivia
// CHECK-DAG: "trivia": "
// CHECK-NOT: "kind": "Whitespace"
// CHECK-NOT: "kind": "Directive"

// "no-trivia" mode emits structured token objects but omits all trivia.
// CHECK-LABEL: CST-MODE-no-trivia
// CHECK-DAG: "kind": "ModuleDeclaration"
// CHECK-DAG: "text": "module"
// CHECK-NOT: "trivia"
// CHECK-NOT: "kind": "Whitespace"

// "simple-tokens" mode collapses each token to its bare text value, so tokens
// have no "kind"/"text"/"trivia" wrapper objects at all.
// CHECK-LABEL: CST-MODE-simple-tokens
// CHECK-DAG: "moduleKeyword": "module"
// CHECK-NOT: "trivia"
// CHECK-NOT: "kind": "ModuleKeyword"

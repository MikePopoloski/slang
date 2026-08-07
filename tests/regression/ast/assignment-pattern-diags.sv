// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --diag-json %t --error-limit=0 2>&1 || true
// CHECK-DIAGS: %t

module m;
    typedef struct {
        int scalar;
//          ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(scalar)
        int array[2];
    } st;

    st value = '{real: 1.0};
//             ^^^^^^^^^^^^ AssignmentPatternMissingElements not all elements of array are covered by an assignment pattern key
//             ^^^^^^^^^^^^ AssignmentPatternNoMember member 'scalar' is not covered by any assignment pattern key

    st too_many = '{
//                ^^ WrongNumberAssignmentPatterns assignment pattern for 'st' requires 2 elements but 3 were provided
        1,
//      ^^ - for WrongNumberAssignmentPatterns
        2,
//      ^^ - for WrongNumberAssignmentPatterns
        3
//      ^ - for WrongNumberAssignmentPatterns
    };
//  ^ - for WrongNumberAssignmentPatterns
endmodule

module assignment_pattern_errors;
    event e1 = event'{1};
//             ^^^^^^^^^ BadAssignmentPatternType invalid target type 'event' for assignment pattern
    parameter p = '{1, 2};
//                ^^^^^^^ AssignmentPatternNoContext assignment pattern target type cannot be deduced in this context

    typedef event e_t;
    e_t e2 = '{1};
//           ^^^^ BadAssignmentPatternType invalid target type 'e_t' (aka 'event') for assignment pattern

    int a[int] = '{1, 2};
//               ^^^^^^^ AssignmentPatternAssociativeType assignment pattern for associative array must specify key:value pairs

    typedef real rt;
    typedef struct { int a; rt b; } st;
    st b = '{1};
//         ^^^^ WrongNumberAssignmentPatterns assignment pattern for 'st' requires 2 elements but 1 were provided
    int c[1:2] = '{1};
//               ^^^^ WrongNumberAssignmentPatterns assignment pattern for 'int$[1:2]' requires 2 elements but 1 were provided
    st d = '{default:1, default:2, a:1, a:2, rt:3.14, blah:3, event:1, (1+1):2};
//                      ^^^^^^^ AssignmentPatternKeyDupDefault assignment pattern has multiple default keys
//                                      ^ AssignmentPatternKeyDupName assignment pattern has multiple keys for member 'a'
//                                   ^ NotePreviousDefinition previous definition here - for AssignmentPatternKeyDupName(a)
//                                                    ^^^^ UnknownMember no member named 'blah' in 'st'
//                                                            ^^^^^ AssignmentPatternKeyExpr expression is not a valid assignment pattern member name or type
//                                                                     ^^^^^ AssignmentPatternKeyExpr expression is not a valid assignment pattern member name or type

    int e[] = '{0:1, 0:2, default:1, int:3, -1:2};
//                   ^ AssignmentPatternKeyDupValue assignment pattern has multiple keys for index 0
//                ^ NotePreviousDefinition previous definition here - for AssignmentPatternKeyDupValue(0)
//                                   ^^^ AssignmentPatternDynamicType assignment patterns for dynamic arrays, associative arrays, and queues cannot have type keys
//                                          ^^ ValueMustBePositive value must be positive
    int f[1:2] = '{default:1, default:2, event:1, 9:1};
//                            ^^^^^^^ AssignmentPatternKeyDupDefault assignment pattern has multiple default keys
//                                       ^^^^^ AssignmentPatternKeyExpr expression is not a valid assignment pattern member name or type
//                                                ^ IndexValueInvalid cannot refer to element 9 of 'int$[1:2]'
    int g[] = '{1:1};
//            ^^^^^^ AssignmentPatternMissingElements not all elements of array are covered by an assignment pattern key

    st h = '{-1{0}};
//           ^^ ValueMustBePositive value must be positive
    st i = '{3{1}};
//         ^^^^^^^ WrongNumberAssignmentPatterns assignment pattern for 'st' requires 2 elements but 3 were provided
    int j[1:2] = '{-1{0}};
//                 ^^ ValueMustBePositive value must be positive
    int k[] = '{-1{0}};
//              ^^ ValueMustBePositive value must be positive

    int l[int] = '{default:1, default:2, 3:1, 3:2, int:1};
//                            ^^^^^^^ AssignmentPatternKeyDupDefault assignment pattern has multiple default keys
//                                            ^ AssignmentPatternKeyDupValue assignment pattern has multiple keys for index 3
//                                       ^ NotePreviousDefinition previous definition here - for AssignmentPatternKeyDupValue(3)
//                                                 ^^^ AssignmentPatternDynamicType assignment patterns for dynamic arrays, associative arrays, and queues cannot have type keys

    int m[2][2] = '{real:3.14};
//                ^^^^^^^^^^^^ AssignmentPatternMissingElements not all elements of array are covered by an assignment pattern key
    struct { int i; real r; } n[2] = '{real:3.14};
//                                   ^^^^^^^^^^^^ AssignmentPatternNoMember member 'i' is not covered by any assignment pattern key
//               ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(i)
endmodule

module assignment_pattern_statement;
    typedef struct {
        int scalar;
//          ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(scalar)
        int array[2];
    } st;

    st other;
    initial other = '{real: 1.0};
//                  ^^^^^^^^^^^^ AssignmentPatternMissingElements not all elements of array are covered by an assignment pattern key
//                  ^^^^^^^^^^^^ AssignmentPatternNoMember member 'scalar' is not covered by any assignment pattern key
endmodule

module nested_assignment_pattern_statement;
    typedef struct {
        int present;
        int missing;
//          ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(missing)
    } inner_t;
    typedef struct {
        inner_t inner;
    } outer_t;

    outer_t value;
    initial value = '{inner: '{present: 1}};
//                           ^^^^^^^^^^^^^ AssignmentPatternNoMember member 'missing' is not covered by any assignment pattern key
endmodule

module nested_and_outer_missing_assignment_pattern_statement;
    typedef struct {
        int present;
        int missing;
//          ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(missing)
    } inner_t;
    typedef struct {
        inner_t inner;
        int outer_missing;
//          ^ NoteDeclarationHere declared here - for AssignmentPatternNoMember(outer_missing)
    } outer_t;

    outer_t value;
    initial value = '{inner: '{present: 1}};
//                  ^^^^^^^^^^^^^^^^^^^^^^^ AssignmentPatternNoMember member 'outer_missing' is not covered by any assignment pattern key
//                           ^^^^^^^^^^^^^ AssignmentPatternNoMember member 'missing' is not covered by any assignment pattern key
endmodule

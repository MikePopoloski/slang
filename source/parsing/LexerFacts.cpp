//------------------------------------------------------------------------------
// LexerFacts.cpp
// Random lexer-related utility functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/LexerFacts.h"

#include "slang/parsing/TokenKind.h"
#include "slang/syntax/SyntaxKind.h"

namespace slang::parsing {

using namespace syntax;

// clang-format off
const static flat_hash_map<std::string_view, TokenKind> systemIdentifierKeywords = {
    { "$root", TokenKind::RootSystemName },
    { "$unit", TokenKind::UnitSystemName }
};

#define STANDARD_DIRECTIVES \
    { "begin_keywords", SyntaxKind::BeginKeywordsDirective },                  \
    { "celldefine", SyntaxKind::CellDefineDirective },                         \
    { "default_nettype", SyntaxKind::DefaultNetTypeDirective },                \
    { "define", SyntaxKind::DefineDirective },                                 \
    { "else", SyntaxKind::ElseDirective },                                     \
    { "elsif", SyntaxKind::ElsIfDirective },                                   \
    { "end_keywords", SyntaxKind::EndKeywordsDirective },                      \
    { "endcelldefine", SyntaxKind::EndCellDefineDirective },                   \
    { "endif", SyntaxKind::EndIfDirective },                                   \
    { "ifdef", SyntaxKind::IfDefDirective },                                   \
    { "ifndef", SyntaxKind::IfNDefDirective },                                 \
    { "include", SyntaxKind::IncludeDirective },                               \
    { "line", SyntaxKind::LineDirective },                                     \
    { "nounconnected_drive", SyntaxKind::NoUnconnectedDriveDirective },        \
    { "pragma", SyntaxKind::PragmaDirective },                                 \
    { "resetall", SyntaxKind::ResetAllDirective },                             \
    { "timescale", SyntaxKind::TimeScaleDirective },                           \
    { "unconnected_drive", SyntaxKind::UnconnectedDriveDirective },            \
    { "undef", SyntaxKind::UndefDirective },                                   \
    { "undefineall", SyntaxKind::UndefineAllDirective },                       \
    { "default_decay_time", SyntaxKind::DefaultDecayTimeDirective },           \
    { "default_trireg_strength", SyntaxKind::DefaultTriregStrengthDirective }, \
    { "delay_mode_distributed", SyntaxKind::DelayModeDistributedDirective },   \
    { "delay_mode_path", SyntaxKind::DelayModePathDirective },                 \
    { "delay_mode_unit", SyntaxKind::DelayModeUnitDirective },                 \
    { "delay_mode_zero", SyntaxKind::DelayModeZeroDirective },

const static flat_hash_map<std::string_view, SyntaxKind> directiveTable = {
    STANDARD_DIRECTIVES
};

const static flat_hash_map<std::string_view, SyntaxKind> directivesWithLegacyProtect = {
    STANDARD_DIRECTIVES
    { "protect", SyntaxKind::ProtectDirective },
    { "endprotect", SyntaxKind::EndProtectDirective },
    { "protected", SyntaxKind::ProtectedDirective },
    { "endprotected", SyntaxKind::EndProtectedDirective }
};

const static flat_hash_map<std::string_view, KeywordVersion> keywordVersionTable = {
    { "1364-1995", KeywordVersion::v1364_1995 },
    { "1364-2001-noconfig", KeywordVersion::v1364_2001_noconfig },
    { "1364-2001", KeywordVersion::v1364_2001 },
    { "1364-2005", KeywordVersion::v1364_2005 },
    { "1800-2005", KeywordVersion::v1800_2005 },
    { "1800-2009", KeywordVersion::v1800_2009 },
    { "1800-2012", KeywordVersion::v1800_2012 },
    { "1800-2017", KeywordVersion::v1800_2017 },
    { "1800-2023", KeywordVersion::v1800_2023 }
};

// Lists of keywords, separated by the specification in which they were first introduced
#define KEYWORDS_1364_1995 \
    { "always", TokenKind::AlwaysKeyword },\
    { "and", TokenKind::AndKeyword },\
    { "assign", TokenKind::AssignKeyword },\
    { "begin", TokenKind::BeginKeyword },\
    { "buf", TokenKind::BufKeyword },\
    { "bufif0", TokenKind::BufIf0Keyword },\
    { "bufif1", TokenKind::BufIf1Keyword },\
    { "case", TokenKind::CaseKeyword },\
    { "casex", TokenKind::CaseXKeyword },\
    { "casez", TokenKind::CaseZKeyword },\
    { "cmos", TokenKind::CmosKeyword },\
    { "deassign", TokenKind::DeassignKeyword },\
    { "default", TokenKind::DefaultKeyword },\
    { "defparam", TokenKind::DefParamKeyword },\
    { "disable", TokenKind::DisableKeyword },\
    { "edge", TokenKind::EdgeKeyword },\
    { "else", TokenKind::ElseKeyword },\
    { "end", TokenKind::EndKeyword },\
    { "endcase", TokenKind::EndCaseKeyword },\
    { "endfunction", TokenKind::EndFunctionKeyword },\
    { "endmodule", TokenKind::EndModuleKeyword },\
    { "endprimitive", TokenKind::EndPrimitiveKeyword },\
    { "endspecify", TokenKind::EndSpecifyKeyword },\
    { "endtable", TokenKind::EndTableKeyword },\
    { "endtask", TokenKind::EndTaskKeyword },\
    { "event", TokenKind::EventKeyword },\
    { "for", TokenKind::ForKeyword },\
    { "force", TokenKind::ForceKeyword },\
    { "forever", TokenKind::ForeverKeyword },\
    { "fork", TokenKind::ForkKeyword },\
    { "function", TokenKind::FunctionKeyword },\
    { "highz0", TokenKind::HighZ0Keyword },\
    { "highz1", TokenKind::HighZ1Keyword },\
    { "if", TokenKind::IfKeyword },\
    { "ifnone", TokenKind::IfNoneKeyword },\
    { "initial", TokenKind::InitialKeyword },\
    { "inout", TokenKind::InOutKeyword },\
    { "input", TokenKind::InputKeyword },\
    { "integer", TokenKind::IntegerKeyword },\
    { "join", TokenKind::JoinKeyword },\
    { "large", TokenKind::LargeKeyword },\
    { "macromodule", TokenKind::MacromoduleKeyword },\
    { "medium", TokenKind::MediumKeyword },\
    { "module", TokenKind::ModuleKeyword },\
    { "nand", TokenKind::NandKeyword },\
    { "negedge", TokenKind::NegEdgeKeyword },\
    { "nmos", TokenKind::NmosKeyword },\
    { "nor", TokenKind::NorKeyword },\
    { "not", TokenKind::NotKeyword },\
    { "notif0", TokenKind::NotIf0Keyword },\
    { "notif1", TokenKind::NotIf1Keyword },\
    { "or", TokenKind::OrKeyword },\
    { "output", TokenKind::OutputKeyword },\
    { "parameter", TokenKind::ParameterKeyword },\
    { "pmos", TokenKind::PmosKeyword },\
    { "posedge", TokenKind::PosEdgeKeyword },\
    { "primitive", TokenKind::PrimitiveKeyword },\
    { "pull0", TokenKind::Pull0Keyword },\
    { "pull1", TokenKind::Pull1Keyword },\
    { "pulldown", TokenKind::PullDownKeyword },\
    { "pullup", TokenKind::PullUpKeyword },\
    { "rcmos", TokenKind::RcmosKeyword },\
    { "real", TokenKind::RealKeyword },\
    { "realtime", TokenKind::RealTimeKeyword },\
    { "reg", TokenKind::RegKeyword },\
    { "release", TokenKind::ReleaseKeyword },\
    { "repeat", TokenKind::RepeatKeyword },\
    { "rnmos", TokenKind::RnmosKeyword },\
    { "rpmos", TokenKind::RpmosKeyword },\
    { "rtran", TokenKind::RtranKeyword },\
    { "rtranif0", TokenKind::RtranIf0Keyword },\
    { "rtranif1", TokenKind::RtranIf1Keyword },\
    { "scalared", TokenKind::ScalaredKeyword },\
    { "small", TokenKind::SmallKeyword },\
    { "specify", TokenKind::SpecifyKeyword },\
    { "specparam", TokenKind::SpecParamKeyword },\
    { "strong0", TokenKind::Strong0Keyword },\
    { "strong1", TokenKind::Strong1Keyword },\
    { "supply0", TokenKind::Supply0Keyword },\
    { "supply1", TokenKind::Supply1Keyword },\
    { "table", TokenKind::TableKeyword },\
    { "task", TokenKind::TaskKeyword },\
    { "time", TokenKind::TimeKeyword },\
    { "tran", TokenKind::TranKeyword },\
    { "tranif0", TokenKind::TranIf0Keyword },\
    { "tranif1", TokenKind::TranIf1Keyword },\
    { "tri", TokenKind::TriKeyword },\
    { "tri0", TokenKind::Tri0Keyword },\
    { "tri1", TokenKind::Tri1Keyword },\
    { "triand", TokenKind::TriAndKeyword },\
    { "trior", TokenKind::TriOrKeyword },\
    { "trireg", TokenKind::TriRegKeyword },\
    { "vectored", TokenKind::VectoredKeyword },\
    { "wait", TokenKind::WaitKeyword },\
    { "wand", TokenKind::WAndKeyword },\
    { "weak0", TokenKind::Weak0Keyword },\
    { "weak1", TokenKind::Weak1Keyword },\
    { "while", TokenKind::WhileKeyword },\
    { "wire", TokenKind::WireKeyword },\
    { "wor", TokenKind::WOrKeyword },\
    { "xor", TokenKind::XorKeyword },\
    { "xnor", TokenKind::XnorKeyword }

#define NEWKEYWORDS_1364_2001_noconfig \
    { "automatic", TokenKind::AutomaticKeyword },\
    { "endgenerate", TokenKind::EndGenerateKeyword },\
    { "generate", TokenKind::GenerateKeyword },\
    { "genvar", TokenKind::GenVarKeyword },\
    { "ifnone", TokenKind::IfNoneKeyword },\
    { "localparam", TokenKind::LocalParamKeyword },\
    { "noshowcancelled", TokenKind::NoShowCancelledKeyword },\
    { "pulsestyle_ondetect", TokenKind::PulseStyleOnDetectKeyword },\
    { "pulsestyle_onevent", TokenKind::PulseStyleOnEventKeyword },\
    { "showcancelled", TokenKind::ShowCancelledKeyword },\
    { "signed", TokenKind::SignedKeyword },\
    { "unsigned", TokenKind::UnsignedKeyword }

#define NEWKEYWORDS_1364_2001 \
    { "cell", TokenKind::CellKeyword },\
    { "config", TokenKind::ConfigKeyword },\
    { "design", TokenKind::DesignKeyword },\
    { "endconfig", TokenKind::EndConfigKeyword },\
    { "incdir", TokenKind::IncDirKeyword },\
    { "include", TokenKind::IncludeKeyword },\
    { "instance", TokenKind::InstanceKeyword },\
    { "liblist", TokenKind::LibListKeyword },\
    { "library", TokenKind::LibraryKeyword },\
    { "use", TokenKind::UseKeyword }

#define NEWKEYWORDS_1364_2005 \
    { "uwire", TokenKind::UWireKeyword }

#define NEWKEYWORDS_1800_2005 \
    { "alias", TokenKind::AliasKeyword },\
    { "always_comb", TokenKind::AlwaysCombKeyword },\
    { "always_ff", TokenKind::AlwaysFFKeyword },\
    { "always_latch", TokenKind::AlwaysLatchKeyword },\
    { "assert", TokenKind::AssertKeyword },\
    { "assume", TokenKind::AssumeKeyword },\
    { "before", TokenKind::BeforeKeyword },\
    { "bind", TokenKind::BindKeyword },\
    { "bins", TokenKind::BinsKeyword },\
    { "binsof", TokenKind::BinsOfKeyword },\
    { "bit", TokenKind::BitKeyword },\
    { "break", TokenKind::BreakKeyword },\
    { "byte", TokenKind::ByteKeyword },\
    { "chandle", TokenKind::CHandleKeyword },\
    { "class", TokenKind::ClassKeyword },\
    { "clocking", TokenKind::ClockingKeyword },\
    { "const", TokenKind::ConstKeyword },\
    { "constraint", TokenKind::ConstraintKeyword },\
    { "context", TokenKind::ContextKeyword },\
    { "continue", TokenKind::ContinueKeyword },\
    { "cover", TokenKind::CoverKeyword },\
    { "covergroup", TokenKind::CoverGroupKeyword },\
    { "coverpoint", TokenKind::CoverPointKeyword },\
    { "cross", TokenKind::CrossKeyword },\
    { "dist", TokenKind::DistKeyword },\
    { "do", TokenKind::DoKeyword },\
    { "endclass", TokenKind::EndClassKeyword },\
    { "endclocking", TokenKind::EndClockingKeyword },\
    { "endgroup", TokenKind::EndGroupKeyword },\
    { "endinterface", TokenKind::EndInterfaceKeyword },\
    { "endpackage", TokenKind::EndPackageKeyword },\
    { "endprogram", TokenKind::EndProgramKeyword },\
    { "endproperty", TokenKind::EndPropertyKeyword },\
    { "endsequence", TokenKind::EndSequenceKeyword },\
    { "enum", TokenKind::EnumKeyword },\
    { "expect", TokenKind::ExpectKeyword },\
    { "export", TokenKind::ExportKeyword },\
    { "extends", TokenKind::ExtendsKeyword },\
    { "extern", TokenKind::ExternKeyword },\
    { "final", TokenKind::FinalKeyword },\
    { "first_match", TokenKind::FirstMatchKeyword },\
    { "foreach", TokenKind::ForeachKeyword },\
    { "forkjoin", TokenKind::ForkJoinKeyword },\
    { "iff", TokenKind::IffKeyword },\
    { "ignore_bins", TokenKind::IgnoreBinsKeyword },\
    { "illegal_bins", TokenKind::IllegalBinsKeyword },\
    { "import", TokenKind::ImportKeyword },\
    { "inside", TokenKind::InsideKeyword },\
    { "int", TokenKind::IntKeyword },\
    { "interface", TokenKind::InterfaceKeyword },\
    { "intersect", TokenKind::IntersectKeyword },\
    { "join_any", TokenKind::JoinAnyKeyword },\
    { "join_none", TokenKind::JoinNoneKeyword },\
    { "local", TokenKind::LocalKeyword },\
    { "logic", TokenKind::LogicKeyword },\
    { "longint", TokenKind::LongIntKeyword },\
    { "matches", TokenKind::MatchesKeyword },\
    { "modport", TokenKind::ModPortKeyword },\
    { "new", TokenKind::NewKeyword },\
    { "null", TokenKind::NullKeyword },\
    { "package", TokenKind::PackageKeyword },\
    { "packed", TokenKind::PackedKeyword },\
    { "priority", TokenKind::PriorityKeyword },\
    { "program", TokenKind::ProgramKeyword },\
    { "property", TokenKind::PropertyKeyword },\
    { "protected", TokenKind::ProtectedKeyword },\
    { "pure", TokenKind::PureKeyword },\
    { "rand", TokenKind::RandKeyword },\
    { "randc", TokenKind::RandCKeyword },\
    { "randcase", TokenKind::RandCaseKeyword },\
    { "randsequence", TokenKind::RandSequenceKeyword },\
    { "ref", TokenKind::RefKeyword },\
    { "return", TokenKind::ReturnKeyword },\
    { "sequence", TokenKind::SequenceKeyword },\
    { "shortint", TokenKind::ShortIntKeyword },\
    { "shortreal", TokenKind::ShortRealKeyword },\
    { "solve", TokenKind::SolveKeyword },\
    { "static", TokenKind::StaticKeyword },\
    { "string", TokenKind::StringKeyword },\
    { "struct", TokenKind::StructKeyword },\
    { "super", TokenKind::SuperKeyword },\
    { "tagged", TokenKind::TaggedKeyword },\
    { "this", TokenKind::ThisKeyword },\
    { "throughout", TokenKind::ThroughoutKeyword },\
    { "timeprecision", TokenKind::TimePrecisionKeyword },\
    { "timeunit", TokenKind::TimeUnitKeyword },\
    { "type", TokenKind::TypeKeyword },\
    { "typedef", TokenKind::TypedefKeyword },\
    { "union", TokenKind::UnionKeyword },\
    { "unique", TokenKind::UniqueKeyword },\
    { "var", TokenKind::VarKeyword },\
    { "virtual", TokenKind::VirtualKeyword },\
    { "void", TokenKind::VoidKeyword },\
    { "wait_order", TokenKind::WaitOrderKeyword },\
    { "wildcard", TokenKind::WildcardKeyword },\
    { "with", TokenKind::WithKeyword },\
    { "within", TokenKind::WithinKeyword }

#define NEWKEYWORDS_1800_2009 \
    { "accept_on", TokenKind::AcceptOnKeyword },\
    { "checker", TokenKind::CheckerKeyword },\
    { "endchecker", TokenKind::EndCheckerKeyword },\
    { "eventually", TokenKind::EventuallyKeyword },\
    { "global", TokenKind::GlobalKeyword },\
    { "implies", TokenKind::ImpliesKeyword },\
    { "let", TokenKind::LetKeyword },\
    { "nexttime", TokenKind::NextTimeKeyword },\
    { "reject_on", TokenKind::RejectOnKeyword },\
    { "restrict", TokenKind::RestrictKeyword },\
    { "s_always", TokenKind::SAlwaysKeyword },\
    { "s_eventually", TokenKind::SEventuallyKeyword },\
    { "s_nexttime", TokenKind::SNextTimeKeyword },\
    { "s_until", TokenKind::SUntilKeyword },\
    { "s_until_with", TokenKind::SUntilWithKeyword },\
    { "strong", TokenKind::StrongKeyword },\
    { "sync_accept_on", TokenKind::SyncAcceptOnKeyword },\
    { "sync_reject_on", TokenKind::SyncRejectOnKeyword },\
    { "unique0", TokenKind::Unique0Keyword },\
    { "until", TokenKind::UntilKeyword },\
    { "until_with", TokenKind::UntilWithKeyword },\
    { "untyped", TokenKind::UntypedKeyword },\
    { "weak", TokenKind::WeakKeyword }

#define NEWKEYWORDS_1800_2012 \
    { "implements", TokenKind::ImplementsKeyword },\
    { "interconnect", TokenKind::InterconnectKeyword },\
    { "nettype", TokenKind::NetTypeKeyword },\
    { "soft", TokenKind::SoftKeyword }

// We maintain a separate table of keywords for all the various specifications,
// to allow for easy switching between them when requested
const static flat_hash_map<std::string_view, TokenKind> allKeywords[9] =
{ { // IEEE 1364-1995
    KEYWORDS_1364_1995
}, { // IEEE 1364-2001-noconfig
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig
}, { // IEEE 1364-2001
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001
}, { // IEEE 1364-2005
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005
}, { // IEEE 1800-2005
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005,
    NEWKEYWORDS_1800_2005
}, { // IEEE 1800-2009
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005,
    NEWKEYWORDS_1800_2005,
    NEWKEYWORDS_1800_2009
}, { // IEEE 1800-2012
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005,
    NEWKEYWORDS_1800_2005,
    NEWKEYWORDS_1800_2009,
    NEWKEYWORDS_1800_2012
}, { // IEEE 1800-2017
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005,
    NEWKEYWORDS_1800_2005,
    NEWKEYWORDS_1800_2009,
    NEWKEYWORDS_1800_2012
}, { // IEEE 1800-2023
    KEYWORDS_1364_1995,
    NEWKEYWORDS_1364_2001_noconfig,
    NEWKEYWORDS_1364_2001,
    NEWKEYWORDS_1364_2005,
    NEWKEYWORDS_1800_2005,
    NEWKEYWORDS_1800_2009,
    NEWKEYWORDS_1800_2012
} };

// clang-format on
bool LexerFacts::isKeyword(TokenKind kind) {
    switch (kind) {
        case TokenKind::OneStep:
        case TokenKind::AcceptOnKeyword:
        case TokenKind::AliasKeyword:
        case TokenKind::AlwaysKeyword:
        case TokenKind::AlwaysCombKeyword:
        case TokenKind::AlwaysFFKeyword:
        case TokenKind::AlwaysLatchKeyword:
        case TokenKind::AndKeyword:
        case TokenKind::AssertKeyword:
        case TokenKind::AssignKeyword:
        case TokenKind::AssumeKeyword:
        case TokenKind::AutomaticKeyword:
        case TokenKind::BeforeKeyword:
        case TokenKind::BeginKeyword:
        case TokenKind::BindKeyword:
        case TokenKind::BinsKeyword:
        case TokenKind::BinsOfKeyword:
        case TokenKind::BitKeyword:
        case TokenKind::BreakKeyword:
        case TokenKind::BufKeyword:
        case TokenKind::BufIf0Keyword:
        case TokenKind::BufIf1Keyword:
        case TokenKind::ByteKeyword:
        case TokenKind::CaseKeyword:
        case TokenKind::CaseXKeyword:
        case TokenKind::CaseZKeyword:
        case TokenKind::CellKeyword:
        case TokenKind::CHandleKeyword:
        case TokenKind::CheckerKeyword:
        case TokenKind::ClassKeyword:
        case TokenKind::ClockingKeyword:
        case TokenKind::CmosKeyword:
        case TokenKind::ConfigKeyword:
        case TokenKind::ConstKeyword:
        case TokenKind::ConstraintKeyword:
        case TokenKind::ContextKeyword:
        case TokenKind::ContinueKeyword:
        case TokenKind::CoverKeyword:
        case TokenKind::CoverGroupKeyword:
        case TokenKind::CoverPointKeyword:
        case TokenKind::CrossKeyword:
        case TokenKind::DeassignKeyword:
        case TokenKind::DefaultKeyword:
        case TokenKind::DefParamKeyword:
        case TokenKind::DesignKeyword:
        case TokenKind::DisableKeyword:
        case TokenKind::DistKeyword:
        case TokenKind::DoKeyword:
        case TokenKind::EdgeKeyword:
        case TokenKind::ElseKeyword:
        case TokenKind::EndKeyword:
        case TokenKind::EndCaseKeyword:
        case TokenKind::EndCheckerKeyword:
        case TokenKind::EndClassKeyword:
        case TokenKind::EndClockingKeyword:
        case TokenKind::EndConfigKeyword:
        case TokenKind::EndFunctionKeyword:
        case TokenKind::EndGenerateKeyword:
        case TokenKind::EndGroupKeyword:
        case TokenKind::EndInterfaceKeyword:
        case TokenKind::EndModuleKeyword:
        case TokenKind::EndPackageKeyword:
        case TokenKind::EndPrimitiveKeyword:
        case TokenKind::EndProgramKeyword:
        case TokenKind::EndPropertyKeyword:
        case TokenKind::EndSpecifyKeyword:
        case TokenKind::EndSequenceKeyword:
        case TokenKind::EndTableKeyword:
        case TokenKind::EndTaskKeyword:
        case TokenKind::EnumKeyword:
        case TokenKind::EventKeyword:
        case TokenKind::EventuallyKeyword:
        case TokenKind::ExpectKeyword:
        case TokenKind::ExportKeyword:
        case TokenKind::ExtendsKeyword:
        case TokenKind::ExternKeyword:
        case TokenKind::FinalKeyword:
        case TokenKind::FirstMatchKeyword:
        case TokenKind::ForKeyword:
        case TokenKind::ForceKeyword:
        case TokenKind::ForeachKeyword:
        case TokenKind::ForeverKeyword:
        case TokenKind::ForkKeyword:
        case TokenKind::ForkJoinKeyword:
        case TokenKind::FunctionKeyword:
        case TokenKind::GenerateKeyword:
        case TokenKind::GenVarKeyword:
        case TokenKind::GlobalKeyword:
        case TokenKind::HighZ0Keyword:
        case TokenKind::HighZ1Keyword:
        case TokenKind::IfKeyword:
        case TokenKind::IffKeyword:
        case TokenKind::IfNoneKeyword:
        case TokenKind::IgnoreBinsKeyword:
        case TokenKind::IllegalBinsKeyword:
        case TokenKind::ImplementsKeyword:
        case TokenKind::ImpliesKeyword:
        case TokenKind::ImportKeyword:
        case TokenKind::IncDirKeyword:
        case TokenKind::IncludeKeyword:
        case TokenKind::InitialKeyword:
        case TokenKind::InOutKeyword:
        case TokenKind::InputKeyword:
        case TokenKind::InsideKeyword:
        case TokenKind::InstanceKeyword:
        case TokenKind::IntKeyword:
        case TokenKind::IntegerKeyword:
        case TokenKind::InterconnectKeyword:
        case TokenKind::InterfaceKeyword:
        case TokenKind::IntersectKeyword:
        case TokenKind::JoinKeyword:
        case TokenKind::JoinAnyKeyword:
        case TokenKind::JoinNoneKeyword:
        case TokenKind::LargeKeyword:
        case TokenKind::LetKeyword:
        case TokenKind::LibListKeyword:
        case TokenKind::LibraryKeyword:
        case TokenKind::LocalKeyword:
        case TokenKind::LocalParamKeyword:
        case TokenKind::LogicKeyword:
        case TokenKind::LongIntKeyword:
        case TokenKind::MacromoduleKeyword:
        case TokenKind::MatchesKeyword:
        case TokenKind::MediumKeyword:
        case TokenKind::ModPortKeyword:
        case TokenKind::ModuleKeyword:
        case TokenKind::NandKeyword:
        case TokenKind::NegEdgeKeyword:
        case TokenKind::NetTypeKeyword:
        case TokenKind::NewKeyword:
        case TokenKind::NextTimeKeyword:
        case TokenKind::NmosKeyword:
        case TokenKind::NorKeyword:
        case TokenKind::NoShowCancelledKeyword:
        case TokenKind::NotKeyword:
        case TokenKind::NotIf0Keyword:
        case TokenKind::NotIf1Keyword:
        case TokenKind::NullKeyword:
        case TokenKind::OrKeyword:
        case TokenKind::OutputKeyword:
        case TokenKind::PackageKeyword:
        case TokenKind::PackedKeyword:
        case TokenKind::ParameterKeyword:
        case TokenKind::PmosKeyword:
        case TokenKind::PosEdgeKeyword:
        case TokenKind::PrimitiveKeyword:
        case TokenKind::PriorityKeyword:
        case TokenKind::ProgramKeyword:
        case TokenKind::PropertyKeyword:
        case TokenKind::ProtectedKeyword:
        case TokenKind::Pull0Keyword:
        case TokenKind::Pull1Keyword:
        case TokenKind::PullDownKeyword:
        case TokenKind::PullUpKeyword:
        case TokenKind::PulseStyleOnDetectKeyword:
        case TokenKind::PulseStyleOnEventKeyword:
        case TokenKind::PureKeyword:
        case TokenKind::RandKeyword:
        case TokenKind::RandCKeyword:
        case TokenKind::RandCaseKeyword:
        case TokenKind::RandSequenceKeyword:
        case TokenKind::RcmosKeyword:
        case TokenKind::RealKeyword:
        case TokenKind::RealTimeKeyword:
        case TokenKind::RefKeyword:
        case TokenKind::RegKeyword:
        case TokenKind::RejectOnKeyword:
        case TokenKind::ReleaseKeyword:
        case TokenKind::RepeatKeyword:
        case TokenKind::RestrictKeyword:
        case TokenKind::ReturnKeyword:
        case TokenKind::RnmosKeyword:
        case TokenKind::RpmosKeyword:
        case TokenKind::RtranKeyword:
        case TokenKind::RtranIf0Keyword:
        case TokenKind::RtranIf1Keyword:
        case TokenKind::SAlwaysKeyword:
        case TokenKind::SEventuallyKeyword:
        case TokenKind::SNextTimeKeyword:
        case TokenKind::SUntilKeyword:
        case TokenKind::SUntilWithKeyword:
        case TokenKind::ScalaredKeyword:
        case TokenKind::SequenceKeyword:
        case TokenKind::ShortIntKeyword:
        case TokenKind::ShortRealKeyword:
        case TokenKind::ShowCancelledKeyword:
        case TokenKind::SignedKeyword:
        case TokenKind::SmallKeyword:
        case TokenKind::SoftKeyword:
        case TokenKind::SolveKeyword:
        case TokenKind::SpecifyKeyword:
        case TokenKind::SpecParamKeyword:
        case TokenKind::StaticKeyword:
        case TokenKind::StringKeyword:
        case TokenKind::StrongKeyword:
        case TokenKind::Strong0Keyword:
        case TokenKind::Strong1Keyword:
        case TokenKind::StructKeyword:
        case TokenKind::SuperKeyword:
        case TokenKind::Supply0Keyword:
        case TokenKind::Supply1Keyword:
        case TokenKind::SyncAcceptOnKeyword:
        case TokenKind::SyncRejectOnKeyword:
        case TokenKind::TableKeyword:
        case TokenKind::TaggedKeyword:
        case TokenKind::TaskKeyword:
        case TokenKind::ThisKeyword:
        case TokenKind::ThroughoutKeyword:
        case TokenKind::TimeKeyword:
        case TokenKind::TimePrecisionKeyword:
        case TokenKind::TimeUnitKeyword:
        case TokenKind::TranKeyword:
        case TokenKind::TranIf0Keyword:
        case TokenKind::TranIf1Keyword:
        case TokenKind::TriKeyword:
        case TokenKind::Tri0Keyword:
        case TokenKind::Tri1Keyword:
        case TokenKind::TriAndKeyword:
        case TokenKind::TriOrKeyword:
        case TokenKind::TriRegKeyword:
        case TokenKind::TypeKeyword:
        case TokenKind::TypedefKeyword:
        case TokenKind::UnionKeyword:
        case TokenKind::UniqueKeyword:
        case TokenKind::Unique0Keyword:
        case TokenKind::UnsignedKeyword:
        case TokenKind::UntilKeyword:
        case TokenKind::UntilWithKeyword:
        case TokenKind::UntypedKeyword:
        case TokenKind::UseKeyword:
        case TokenKind::UWireKeyword:
        case TokenKind::VarKeyword:
        case TokenKind::VectoredKeyword:
        case TokenKind::VirtualKeyword:
        case TokenKind::VoidKeyword:
        case TokenKind::WaitKeyword:
        case TokenKind::WaitOrderKeyword:
        case TokenKind::WAndKeyword:
        case TokenKind::WeakKeyword:
        case TokenKind::Weak0Keyword:
        case TokenKind::Weak1Keyword:
        case TokenKind::WhileKeyword:
        case TokenKind::WildcardKeyword:
        case TokenKind::WireKeyword:
        case TokenKind::WithKeyword:
        case TokenKind::WithinKeyword:
        case TokenKind::WOrKeyword:
        case TokenKind::XnorKeyword:
        case TokenKind::XorKeyword:
            return true;
        default:
            return false;
    }
}

TokenKind LexerFacts::getSystemKeywordKind(std::string_view text) {
    if (auto it = systemIdentifierKeywords.find(text); it != systemIdentifierKeywords.end())
        return it->second;
    return TokenKind::Unknown;
}

SyntaxKind LexerFacts::getDirectiveKind(std::string_view directive, bool enableLegacyProtect) {
    auto& table = enableLegacyProtect ? directivesWithLegacyProtect : directiveTable;
    if (auto it = table.find(directive); it != table.end())
        return it->second;
    return SyntaxKind::MacroUsage;
}

KeywordVersion LexerFacts::getDefaultKeywordVersion(LanguageVersion languageVersion) {
    switch (languageVersion) {
        case LanguageVersion::v1800_2017:
            return KeywordVersion::v1800_2017;
        case LanguageVersion::v1800_2023:
            return KeywordVersion::v1800_2023;
        default:
            SLANG_UNREACHABLE;
    }
}

std::optional<KeywordVersion> LexerFacts::getKeywordVersion(std::string_view text) {
    if (auto it = keywordVersionTable.find(text); it != keywordVersionTable.end())
        return it->second;
    return std::nullopt;
}

const flat_hash_map<std::string_view, TokenKind>* LexerFacts::getKeywordTable(
    KeywordVersion version) {
    return &allKeywords[(uint8_t)version];
}

// clang-format off
std::string_view LexerFacts::getDirectiveText(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::BeginKeywordsDirective: return "`begin_keywords";
        case SyntaxKind::CellDefineDirective: return "`celldefine";
        case SyntaxKind::DefaultNetTypeDirective: return "`default_nettype";
        case SyntaxKind::DefineDirective: return "`define";
        case SyntaxKind::ElseDirective: return "`else";
        case SyntaxKind::ElsIfDirective: return "`elsif";
        case SyntaxKind::EndKeywordsDirective: return "`end_keywords";
        case SyntaxKind::EndCellDefineDirective: return "`endcelldefine";
        case SyntaxKind::EndIfDirective: return "`endif";
        case SyntaxKind::IfDefDirective: return "`ifdef";
        case SyntaxKind::IfNDefDirective: return "`ifndef";
        case SyntaxKind::IncludeDirective: return "`include";
        case SyntaxKind::LineDirective: return "`line";
        case SyntaxKind::NoUnconnectedDriveDirective: return "`nounconnected_drive";
        case SyntaxKind::PragmaDirective: return "`pragma";
        case SyntaxKind::ResetAllDirective: return "`resetall";
        case SyntaxKind::TimeScaleDirective: return "`timescale";
        case SyntaxKind::UnconnectedDriveDirective: return "`unconnected_drive";
        case SyntaxKind::UndefDirective: return "`undef";
        case SyntaxKind::UndefineAllDirective: return "`undefineall";
        default: return "";
    }
}

std::string_view LexerFacts::getTokenKindText(TokenKind kind) {
    switch (kind) {
        // punctuation
        case TokenKind::Apostrophe: return "'";
        case TokenKind::ApostropheOpenBrace: return "'{";
        case TokenKind::OpenBrace: return "{";
        case TokenKind::CloseBrace: return "}";
        case TokenKind::OpenBracket: return "[";
        case TokenKind::CloseBracket: return "]";
        case TokenKind::OpenParenthesis: return "(";
        case TokenKind::CloseParenthesis: return ")";
        case TokenKind::Semicolon: return ";";
        case TokenKind::Colon: return ":";
        case TokenKind::ColonEquals: return ":=";
        case TokenKind::ColonSlash: return ":/";
        case TokenKind::DoubleColon: return "::";
        case TokenKind::Comma: return ",";
        case TokenKind::Dot: return ".";
        case TokenKind::Slash: return "/";
        case TokenKind::Star: return "*";
        case TokenKind::DoubleStar: return "**";
        case TokenKind::StarArrow: return "*>";
        case TokenKind::Plus: return "+";
        case TokenKind::DoublePlus: return "++";
        case TokenKind::PlusColon: return "+:";
        case TokenKind::PlusDivMinus: return "+/-";
        case TokenKind::PlusModMinus: return "+%-";
        case TokenKind::Minus: return "-";
        case TokenKind::DoubleMinus: return "--";
        case TokenKind::MinusColon: return "-:";
        case TokenKind::MinusArrow: return "->";
        case TokenKind::MinusDoubleArrow: return "->>";
        case TokenKind::Tilde: return "~";
        case TokenKind::TildeAnd: return "~&";
        case TokenKind::TildeOr: return "~|";
        case TokenKind::TildeXor: return "~^";
        case TokenKind::Dollar: return "$";
        case TokenKind::Question: return "?";
        case TokenKind::Hash: return "#";
        case TokenKind::DoubleHash: return "##";
        case TokenKind::HashMinusHash: return "#-#";
        case TokenKind::HashEqualsHash: return "#=#";
        case TokenKind::Xor: return "^";
        case TokenKind::XorTilde: return "^~";
        case TokenKind::Equals: return "=";
        case TokenKind::DoubleEquals: return "==";
        case TokenKind::DoubleEqualsQuestion: return "==?";
        case TokenKind::TripleEquals: return "===";
        case TokenKind::EqualsArrow: return "=>";
        case TokenKind::PlusEqual: return "+=";
        case TokenKind::MinusEqual: return "-=";
        case TokenKind::SlashEqual: return "/=";
        case TokenKind::StarEqual: return "*=";
        case TokenKind::AndEqual: return "&=";
        case TokenKind::OrEqual: return "|=";
        case TokenKind::PercentEqual: return "%=";
        case TokenKind::XorEqual: return "^=";
        case TokenKind::LeftShiftEqual: return "<<=";
        case TokenKind::TripleLeftShiftEqual: return "<<<=";
        case TokenKind::RightShiftEqual: return ">>=";
        case TokenKind::TripleRightShiftEqual: return ">>>=";
        case TokenKind::LeftShift: return "<<";
        case TokenKind::RightShift: return ">>";
        case TokenKind::TripleLeftShift: return "<<<";
        case TokenKind::TripleRightShift: return ">>>";
        case TokenKind::Exclamation: return "!";
        case TokenKind::ExclamationEquals: return "!=";
        case TokenKind::ExclamationEqualsQuestion: return "!=?";
        case TokenKind::ExclamationDoubleEquals: return "!==";
        case TokenKind::Percent: return "%";
        case TokenKind::LessThan: return "<";
        case TokenKind::LessThanEquals: return "<=";
        case TokenKind::LessThanMinusArrow: return "<->";
        case TokenKind::GreaterThan: return ">";
        case TokenKind::GreaterThanEquals: return ">=";
        case TokenKind::Or: return "|";
        case TokenKind::DoubleOr: return "||";
        case TokenKind::OrMinusArrow: return "|->";
        case TokenKind::OrEqualsArrow: return "|=>";
        case TokenKind::At: return "@";
        case TokenKind::DoubleAt: return "@@";
        case TokenKind::And: return "&";
        case TokenKind::DoubleAnd: return "&&";
        case TokenKind::TripleAnd: return "&&&";

        // keywords
        case TokenKind::OneStep: return "1step";
        case TokenKind::AcceptOnKeyword: return "accept_on";
        case TokenKind::AliasKeyword: return "alias";
        case TokenKind::AlwaysKeyword: return "always";
        case TokenKind::AlwaysCombKeyword: return "always_comb";
        case TokenKind::AlwaysFFKeyword: return "always_ff";
        case TokenKind::AlwaysLatchKeyword: return "always_latch";
        case TokenKind::AndKeyword: return "and";
        case TokenKind::AssertKeyword: return "assert";
        case TokenKind::AssignKeyword: return "assign";
        case TokenKind::AssumeKeyword: return "assume";
        case TokenKind::AutomaticKeyword: return "automatic";
        case TokenKind::BeforeKeyword: return "before";
        case TokenKind::BeginKeyword: return "begin";
        case TokenKind::BindKeyword: return "bind";
        case TokenKind::BinsKeyword: return "bins";
        case TokenKind::BinsOfKeyword: return "binsof";
        case TokenKind::BitKeyword: return "bit";
        case TokenKind::BreakKeyword: return "break";
        case TokenKind::BufKeyword: return "buf";
        case TokenKind::BufIf0Keyword: return "bufif0";
        case TokenKind::BufIf1Keyword: return "bufif1";
        case TokenKind::ByteKeyword: return "byte";
        case TokenKind::CaseKeyword: return "case";
        case TokenKind::CaseXKeyword: return "casex";
        case TokenKind::CaseZKeyword: return "casez";
        case TokenKind::CellKeyword: return "cell";
        case TokenKind::CHandleKeyword: return "chandle";
        case TokenKind::CheckerKeyword: return "checker";
        case TokenKind::ClassKeyword: return "class";
        case TokenKind::ClockingKeyword: return "clocking";
        case TokenKind::CmosKeyword: return "cmos";
        case TokenKind::ConfigKeyword: return "config";
        case TokenKind::ConstKeyword: return "const";
        case TokenKind::ConstraintKeyword: return "constraint";
        case TokenKind::ContextKeyword: return "context";
        case TokenKind::ContinueKeyword: return "continue";
        case TokenKind::CoverKeyword: return "cover";
        case TokenKind::CoverGroupKeyword: return "covergroup";
        case TokenKind::CoverPointKeyword: return "coverpoint";
        case TokenKind::CrossKeyword: return "cross";
        case TokenKind::DeassignKeyword: return "deassign";
        case TokenKind::DefaultKeyword: return "default";
        case TokenKind::DefParamKeyword: return "defparam";
        case TokenKind::DesignKeyword: return "design";
        case TokenKind::DisableKeyword: return "disable";
        case TokenKind::DistKeyword: return "dist";
        case TokenKind::DoKeyword: return "do";
        case TokenKind::EdgeKeyword: return "edge";
        case TokenKind::ElseKeyword: return "else";
        case TokenKind::EndKeyword: return "end";
        case TokenKind::EndCaseKeyword: return "endcase";
        case TokenKind::EndCheckerKeyword: return "endchecker";
        case TokenKind::EndClassKeyword: return "endclass";
        case TokenKind::EndClockingKeyword: return "endclocking";
        case TokenKind::EndConfigKeyword: return "endconfig";
        case TokenKind::EndFunctionKeyword: return "endfunction";
        case TokenKind::EndGenerateKeyword: return "endgenerate";
        case TokenKind::EndGroupKeyword: return "endgroup";
        case TokenKind::EndInterfaceKeyword: return "endinterface";
        case TokenKind::EndModuleKeyword: return "endmodule";
        case TokenKind::EndPackageKeyword: return "endpackage";
        case TokenKind::EndPrimitiveKeyword: return "endprimitive";
        case TokenKind::EndProgramKeyword: return "endprogram";
        case TokenKind::EndPropertyKeyword: return "endproperty";
        case TokenKind::EndSpecifyKeyword: return "endspecify";
        case TokenKind::EndSequenceKeyword: return "endsequence";
        case TokenKind::EndTableKeyword: return "endtable";
        case TokenKind::EndTaskKeyword: return "endtask";
        case TokenKind::EnumKeyword: return "enum";
        case TokenKind::EventKeyword: return "event";
        case TokenKind::EventuallyKeyword: return "eventually";
        case TokenKind::ExpectKeyword: return "expect";
        case TokenKind::ExportKeyword: return "export";
        case TokenKind::ExtendsKeyword: return "extends";
        case TokenKind::ExternKeyword: return "extern";
        case TokenKind::FinalKeyword: return "final";
        case TokenKind::FirstMatchKeyword: return "first_match";
        case TokenKind::ForKeyword: return "for";
        case TokenKind::ForceKeyword: return "force";
        case TokenKind::ForeachKeyword: return "foreach";
        case TokenKind::ForeverKeyword: return "forever";
        case TokenKind::ForkKeyword: return "fork";
        case TokenKind::ForkJoinKeyword: return "forkjoin";
        case TokenKind::FunctionKeyword: return "function";
        case TokenKind::GenerateKeyword: return "generate";
        case TokenKind::GenVarKeyword: return "genvar";
        case TokenKind::GlobalKeyword: return "global";
        case TokenKind::HighZ0Keyword: return "highz0";
        case TokenKind::HighZ1Keyword: return "highz1";
        case TokenKind::IfKeyword: return "if";
        case TokenKind::IffKeyword: return "iff";
        case TokenKind::IfNoneKeyword: return "ifnone";
        case TokenKind::IgnoreBinsKeyword: return "ignore_bins";
        case TokenKind::IllegalBinsKeyword: return "illegal_bins";
        case TokenKind::ImplementsKeyword: return "implements";
        case TokenKind::ImpliesKeyword: return "implies";
        case TokenKind::ImportKeyword: return "import";
        case TokenKind::IncDirKeyword: return "incdir";
        case TokenKind::IncludeKeyword: return "include";
        case TokenKind::InitialKeyword: return "initial";
        case TokenKind::InOutKeyword: return "inout";
        case TokenKind::InputKeyword: return "input";
        case TokenKind::InsideKeyword: return "inside";
        case TokenKind::InstanceKeyword: return "instance";
        case TokenKind::IntKeyword: return "int";
        case TokenKind::IntegerKeyword: return "integer";
        case TokenKind::InterconnectKeyword: return "interconnect";
        case TokenKind::InterfaceKeyword: return "interface";
        case TokenKind::IntersectKeyword: return "intersect";
        case TokenKind::JoinKeyword: return "join";
        case TokenKind::JoinAnyKeyword: return "join_any";
        case TokenKind::JoinNoneKeyword: return "join_none";
        case TokenKind::LargeKeyword: return "large";
        case TokenKind::LetKeyword: return "let";
        case TokenKind::LibListKeyword: return "liblist";
        case TokenKind::LibraryKeyword: return "library";
        case TokenKind::LocalKeyword: return "local";
        case TokenKind::LocalParamKeyword: return "localparam";
        case TokenKind::LogicKeyword: return "logic";
        case TokenKind::LongIntKeyword: return "longint";
        case TokenKind::MacromoduleKeyword: return "macromodule";
        case TokenKind::MatchesKeyword: return "matches";
        case TokenKind::MediumKeyword: return "medium";
        case TokenKind::ModPortKeyword: return "modport";
        case TokenKind::ModuleKeyword: return "module";
        case TokenKind::NandKeyword: return "nand";
        case TokenKind::NegEdgeKeyword: return "negedge";
        case TokenKind::NetTypeKeyword: return "nettype";
        case TokenKind::NewKeyword: return "new";
        case TokenKind::NextTimeKeyword: return "nexttime";
        case TokenKind::NmosKeyword: return "nmos";
        case TokenKind::NorKeyword: return "nor";
        case TokenKind::NoShowCancelledKeyword: return "noshowcancelled";
        case TokenKind::NotKeyword: return "not";
        case TokenKind::NotIf0Keyword: return "notif0";
        case TokenKind::NotIf1Keyword: return "notif1";
        case TokenKind::NullKeyword: return "null";
        case TokenKind::OrKeyword: return "or";
        case TokenKind::OutputKeyword: return "output";
        case TokenKind::PackageKeyword: return "package";
        case TokenKind::PackedKeyword: return "packed";
        case TokenKind::ParameterKeyword: return "parameter";
        case TokenKind::PmosKeyword: return "pmos";
        case TokenKind::PosEdgeKeyword: return "posedge";
        case TokenKind::PrimitiveKeyword: return "primitive";
        case TokenKind::PriorityKeyword: return "priority";
        case TokenKind::ProgramKeyword: return "program";
        case TokenKind::PropertyKeyword: return "property";
        case TokenKind::ProtectedKeyword: return "protected";
        case TokenKind::Pull0Keyword: return "pull0";
        case TokenKind::Pull1Keyword: return "pull1";
        case TokenKind::PullDownKeyword: return "pulldown";
        case TokenKind::PullUpKeyword: return "pullup";
        case TokenKind::PulseStyleOnDetectKeyword: return "pulsestyle_ondetect";
        case TokenKind::PulseStyleOnEventKeyword: return "pulsestyle_onevent";
        case TokenKind::PureKeyword: return "pure";
        case TokenKind::RandKeyword: return "rand";
        case TokenKind::RandCKeyword: return "randc";
        case TokenKind::RandCaseKeyword: return "randcase";
        case TokenKind::RandSequenceKeyword: return "randsequence";
        case TokenKind::RcmosKeyword: return "rcmos";
        case TokenKind::RealKeyword: return "real";
        case TokenKind::RealTimeKeyword: return "realtime";
        case TokenKind::RefKeyword: return "ref";
        case TokenKind::RegKeyword: return "reg";
        case TokenKind::RejectOnKeyword: return "reject_on";
        case TokenKind::ReleaseKeyword: return "release";
        case TokenKind::RepeatKeyword: return "repeat";
        case TokenKind::RestrictKeyword: return "restrict";
        case TokenKind::ReturnKeyword: return "return";
        case TokenKind::RnmosKeyword: return "rnmos";
        case TokenKind::RpmosKeyword: return "rpmos";
        case TokenKind::RtranKeyword: return "rtran";
        case TokenKind::RtranIf0Keyword: return "rtranif0";
        case TokenKind::RtranIf1Keyword: return "rtranif1";
        case TokenKind::SAlwaysKeyword: return "s_always";
        case TokenKind::SEventuallyKeyword: return "s_eventually";
        case TokenKind::SNextTimeKeyword: return "s_nexttime";
        case TokenKind::SUntilKeyword: return "s_until";
        case TokenKind::SUntilWithKeyword: return "s_until_with";
        case TokenKind::ScalaredKeyword: return "scalared";
        case TokenKind::SequenceKeyword: return "sequence";
        case TokenKind::ShortIntKeyword: return "shortint";
        case TokenKind::ShortRealKeyword: return "shortreal";
        case TokenKind::ShowCancelledKeyword: return "showcancelled";
        case TokenKind::SignedKeyword: return "signed";
        case TokenKind::SmallKeyword: return "small";
        case TokenKind::SoftKeyword: return "soft";
        case TokenKind::SolveKeyword: return "solve";
        case TokenKind::SpecifyKeyword: return "specify";
        case TokenKind::SpecParamKeyword: return "specparam";
        case TokenKind::StaticKeyword: return "static";
        case TokenKind::StringKeyword: return "string";
        case TokenKind::StrongKeyword: return "strong";
        case TokenKind::Strong0Keyword: return "strong0";
        case TokenKind::Strong1Keyword: return "strong1";
        case TokenKind::StructKeyword: return "struct";
        case TokenKind::SuperKeyword: return "super";
        case TokenKind::Supply0Keyword: return "supply0";
        case TokenKind::Supply1Keyword: return "supply1";
        case TokenKind::SyncAcceptOnKeyword: return "sync_accept_on";
        case TokenKind::SyncRejectOnKeyword: return "sync_reject_on";
        case TokenKind::TableKeyword: return "table";
        case TokenKind::TaggedKeyword: return "tagged";
        case TokenKind::TaskKeyword: return "task";
        case TokenKind::ThisKeyword: return "this";
        case TokenKind::ThroughoutKeyword: return "throughout";
        case TokenKind::TimeKeyword: return "time";
        case TokenKind::TimePrecisionKeyword: return "timeprecision";
        case TokenKind::TimeUnitKeyword: return "timeunit";
        case TokenKind::TranKeyword: return "tran";
        case TokenKind::TranIf0Keyword: return "tranif0";
        case TokenKind::TranIf1Keyword: return "tranif1";
        case TokenKind::TriKeyword: return "tri";
        case TokenKind::Tri0Keyword: return "tri0";
        case TokenKind::Tri1Keyword: return "tri1";
        case TokenKind::TriAndKeyword: return "triand";
        case TokenKind::TriOrKeyword: return "trior";
        case TokenKind::TriRegKeyword: return "trireg";
        case TokenKind::TypeKeyword: return "type";
        case TokenKind::TypedefKeyword: return "typedef";
        case TokenKind::UnionKeyword: return "union";
        case TokenKind::UniqueKeyword: return "unique";
        case TokenKind::Unique0Keyword: return "unique0";
        case TokenKind::UnsignedKeyword: return "unsigned";
        case TokenKind::UntilKeyword: return "until";
        case TokenKind::UntilWithKeyword: return "until_with";
        case TokenKind::UntypedKeyword: return "untyped";
        case TokenKind::UseKeyword: return "use";
        case TokenKind::UWireKeyword: return "uwire";
        case TokenKind::VarKeyword: return "var";
        case TokenKind::VectoredKeyword: return "vectored";
        case TokenKind::VirtualKeyword: return "virtual";
        case TokenKind::VoidKeyword: return "void";
        case TokenKind::WaitKeyword: return "wait";
        case TokenKind::WaitOrderKeyword: return "wait_order";
        case TokenKind::WAndKeyword: return "wand";
        case TokenKind::WeakKeyword: return "weak";
        case TokenKind::Weak0Keyword: return "weak0";
        case TokenKind::Weak1Keyword: return "weak1";
        case TokenKind::WhileKeyword: return "while";
        case TokenKind::WildcardKeyword: return "wildcard";
        case TokenKind::WireKeyword: return "wire";
        case TokenKind::WithKeyword: return "with";
        case TokenKind::WithinKeyword: return "within";
        case TokenKind::WOrKeyword: return "wor";
        case TokenKind::XnorKeyword: return "xnor";
        case TokenKind::XorKeyword: return "xor";

        // predefined system keywords
        case TokenKind::UnitSystemName: return "$unit";
        case TokenKind::RootSystemName: return "$root";

        // directives
        case TokenKind::MacroQuote: return "`\"";
        case TokenKind::MacroTripleQuote: return "`\"\"\"";
        case TokenKind::MacroEscapedQuote: return "`\\`\"";
        case TokenKind::MacroPaste: return "``";

        default: return "";
    }
}
// clang-format on

} // namespace slang::parsing

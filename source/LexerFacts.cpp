#include <cstdint>
#include <memory>
#include <string>
#include <algorithm>

#include "BumpAllocator.h"
#include "StringTable.h"
#include "Token.h"
#include "Trivia.h"
#include "StringTable.h"

namespace slang {

const static StringTable<TokenKind> systemIdentifierKeywords = {
    { "$root", TokenKind::RootSystemName },
    { "$unit", TokenKind::UnitSystemName }
};

const static StringTable<SyntaxKind> directiveTable = {
    { "`begin_keywords", SyntaxKind::BeginKeywordsDirective },
    { "`celldefine", SyntaxKind::CellDefineDirective },
    { "`default_nettype", SyntaxKind::DefaultNetTypeDirective },
    { "`define", SyntaxKind::DefineDirective },
    { "`else", SyntaxKind::ElseDirective },
    { "`elseif", SyntaxKind::ElseIfDirective },
    { "`end_keywords", SyntaxKind::EndKeywordsDirective },
    { "`endcelldefine", SyntaxKind::EndCellDefineDirective },
    { "`endif", SyntaxKind::EndIfDirective },
    { "`ifdef", SyntaxKind::IfDefDirective },
    { "`ifndef", SyntaxKind::IfNDefDirective },
    { "`include", SyntaxKind::IncludeDirective },
    { "`line", SyntaxKind::LineDirective },
    { "`nounconnected_drive", SyntaxKind::NoUnconnectedDriveDirective },
    { "`pragma", SyntaxKind::PragmaDirective },
    { "`resetall", SyntaxKind::ResetAllDirective },
    { "`timescale", SyntaxKind::TimescaleDirective },
    { "`unconnected_drive", SyntaxKind::UnconnectedDriveDirective },
    { "`undef", SyntaxKind::UndefDirective },
    { "`undefineall", SyntaxKind::UndefineAllDirective }
};

const static StringTable<TokenKind> allKeywords = {
    { "accept_on", TokenKind::AcceptOnKeyword },
    { "alias", TokenKind::AliasKeyword },
    { "always", TokenKind::AlwaysKeyword },
    { "always_comb", TokenKind::AlwaysCombKeyword },
    { "always_ff", TokenKind::AlwaysFFKeyword },
    { "always_latch", TokenKind::AlwaysLatchKeyword },
    { "and", TokenKind::AndKeyword },
    { "assert", TokenKind::AssertKeyword },
    { "assign", TokenKind::AssignKeyword },
    { "assume", TokenKind::AssumeKeyword },
    { "automatic", TokenKind::AutomaticKeyword },
    { "before", TokenKind::BeforeKeyword },
    { "begin", TokenKind::BeginKeyword },
    { "bind", TokenKind::BindKeyword },
    { "bins", TokenKind::BinsKeyword },
    { "binsof", TokenKind::BinsOfKeyword },
    { "bit", TokenKind::BitKeyword },
    { "break", TokenKind::BreakKeyword },
    { "buf", TokenKind::BufKeyword },
    { "bufif0", TokenKind::BufIf0Keyword },
    { "bufif1", TokenKind::BufIf1Keyword },
    { "byte", TokenKind::ByteKeyword },
    { "case", TokenKind::CaseKeyword },
    { "casex", TokenKind::CaseXKeyword },
    { "casez", TokenKind::CaseZKeyword },
    { "cell", TokenKind::CellKeyword },
    { "chandle", TokenKind::CHandleKeyword },
    { "checker", TokenKind::CheckerKeyword },
    { "class", TokenKind::ClassKeyword },
    { "clocking", TokenKind::ClockingKeyword },
    { "cmos", TokenKind::CmosKeyword },
    { "config", TokenKind::ConfigKeyword },
    { "const", TokenKind::ConstKeyword },
    { "constraint", TokenKind::ConstraintKeyword },
    { "context", TokenKind::ContextKeyword },
    { "continue", TokenKind::ContinueKeyword },
    { "cover", TokenKind::CoverKeyword },
    { "covergroup", TokenKind::CoverGroupKeyword },
    { "coverpoint", TokenKind::CoverPointKeyword },
    { "cross", TokenKind::CrossKeyword },
    { "deassign", TokenKind::DeassignKeyword },
    { "default", TokenKind::DefaultKeyword },
    { "defparam", TokenKind::DefParamKeyword },
    { "design", TokenKind::DesignKeyword },
    { "disable", TokenKind::DisableKeyword },
    { "dist", TokenKind::DistKeyword },
    { "do", TokenKind::DoKeyword },
    { "edge", TokenKind::EdgeKeyword },
    { "else", TokenKind::ElseKeyword },
    { "end", TokenKind::EndKeyword },
    { "endcase", TokenKind::EndCaseKeyword },
    { "endchecker", TokenKind::EndCheckerKeyword },
    { "endclass", TokenKind::EndClassKeyword },
    { "endclocking", TokenKind::EndClockingKeyword },
    { "endconfig", TokenKind::EndConfigKeyword },
    { "endfunction", TokenKind::EndFunctionKeyword },
    { "endgenerate", TokenKind::EndGenerateKeyword },
    { "endgroup", TokenKind::EndGroupKeyword },
    { "endinterface", TokenKind::EndInterfaceKeyword },
    { "endmodule", TokenKind::EndModuleKeyword },
    { "endpackage", TokenKind::EndPackageKeyword },
    { "endprimitive", TokenKind::EndPrimitiveKeyword },
    { "endprogram", TokenKind::EndProgramKeyword },
    { "endproperty", TokenKind::EndPropertyKeyword },
    { "endspecify", TokenKind::EndSpecifyKeyword },
    { "endsequence", TokenKind::EndSequenceKeyword },
    { "endtable", TokenKind::EndTableKeyword },
    { "endtask", TokenKind::EndTaskKeyword },
    { "enum", TokenKind::EnumKeyword },
    { "event", TokenKind::EventKeyword },
    { "eventually", TokenKind::EventuallyKeyword },
    { "expect", TokenKind::ExpectKeyword },
    { "export", TokenKind::ExportKeyword },
    { "extends", TokenKind::ExtendsKeyword },
    { "extern", TokenKind::ExternKeyword },
    { "final", TokenKind::FinalKeyword },
    { "first_match", TokenKind::FirstMatchKeyword },
    { "for", TokenKind::ForKeyword },
    { "force", TokenKind::ForceKeyword },
    { "foreach", TokenKind::ForeachKeyword },
    { "forever", TokenKind::ForeverKeyword },
    { "fork", TokenKind::ForkKeyword },
    { "forkjoin", TokenKind::ForkJoinKeyword },
    { "function", TokenKind::FunctionKeyword },
    { "generate", TokenKind::GenerateKeyword },
    { "genvar", TokenKind::GenVarKeyword },
    { "global", TokenKind::GlobalKeyword },
    { "highz0", TokenKind::HighZ0Keyword },
    { "highz1", TokenKind::HighZ1Keyword },
    { "if", TokenKind::IfKeyword },
    { "iff", TokenKind::IffKeyword },
    { "ifnone", TokenKind::IfNoneKeyword },
    { "ignore_bins", TokenKind::IgnoreBinsKeyword },
    { "illegal_bins", TokenKind::IllegalBinsKeyword },
    { "implements", TokenKind::ImplementsKeyword },
    { "implies", TokenKind::ImpliesKeyword },
    { "import", TokenKind::ImportKeyword },
    { "incdir", TokenKind::IncDirKeyword },
    { "include", TokenKind::IncludeKeyword },
    { "initial", TokenKind::InitialKeyword },
    { "inout", TokenKind::InOutKeyword },
    { "input", TokenKind::InputKeyword },
    { "inside", TokenKind::InsideKeyword },
    { "instance", TokenKind::InstanceKeyword },
    { "int", TokenKind::IntKeyword },
    { "integer", TokenKind::IntegerKeyword },
    { "interconnect", TokenKind::InterconnectKeyword },
    { "interface", TokenKind::InterfaceKeyword },
    { "intersect", TokenKind::IntersectKeyword },
    { "join", TokenKind::JoinKeyword },
    { "join_any", TokenKind::JoinAnyKeyword },
    { "join_none", TokenKind::JoinNoneKeyword },
    { "large", TokenKind::LargeKeyword },
    { "let", TokenKind::LetKeyword },
    { "liblist", TokenKind::LibListKeyword },
    { "library", TokenKind::LibraryKeyword },
    { "local", TokenKind::LocalKeyword },
    { "localparam", TokenKind::LocalParamKeyword },
    { "logic", TokenKind::LogicKeyword },
    { "longint", TokenKind::LongIntKeyword },
    { "macromodule", TokenKind::MacromoduleKeyword },
    { "matches", TokenKind::MatchesKeyword },
    { "medium", TokenKind::MediumKeyword },
    { "modport", TokenKind::ModPortKeyword },
    { "module", TokenKind::ModuleKeyword },
    { "nand", TokenKind::NandKeyword },
    { "negedge", TokenKind::NegEdgeKeyword },
    { "nettype", TokenKind::NetTypeKeyword },
    { "new", TokenKind::NewKeyword },
    { "nexttime", TokenKind::NextTimeKeyword },
    { "nmos", TokenKind::NmosKeyword },
    { "nor", TokenKind::NorKeyword },
    { "noshowcancelled", TokenKind::NoShowCancelledKeyword },
    { "not", TokenKind::NotKeyword },
    { "notif0", TokenKind::NotIf0Keyword },
    { "notif1", TokenKind::NotIf1Keyword },
    { "null", TokenKind::NullKeyword },
    { "or", TokenKind::OrKeyword },
    { "output", TokenKind::OutputKeyword },
    { "package", TokenKind::PackageKeyword },
    { "packed", TokenKind::PackedKeyword },
    { "parameter", TokenKind::ParameterKeyword },
    { "pmos", TokenKind::PmosKeyword },
    { "posedge", TokenKind::PosEdgeKeyword },
    { "primitive", TokenKind::PrimitiveKeyword },
    { "priority", TokenKind::PriorityKeyword },
    { "program", TokenKind::ProgramKeyword },
    { "property", TokenKind::PropertyKeyword },
    { "protected", TokenKind::ProtectedKeyword },
    { "pull0", TokenKind::Pull0Keyword },
    { "pull1", TokenKind::Pull1Keyword },
    { "pulldown", TokenKind::PullDownKeyword },
    { "pullup", TokenKind::PullUpKeyword },
    { "pulsestyle_ondetect", TokenKind::PulseStyleOnDetectKeyword },
    { "pulsestyle_onevent", TokenKind::PulseStyleOnEventKeyword },
    { "pure", TokenKind::PureKeyword },
    { "rand", TokenKind::RandKeyword },
    { "randc", TokenKind::RandCKeyword },
    { "randcase", TokenKind::RandCaseKeyword },
    { "randsequence", TokenKind::RandSequenceKeyword },
    { "rcmos", TokenKind::RcmosKeyword },
    { "real", TokenKind::RealKeyword },
    { "realtime", TokenKind::RealTimeKeyword },
    { "ref", TokenKind::RefKeyword },
    { "reg", TokenKind::RegKeyword },
    { "reject_on", TokenKind::RejectOnKeyword },
    { "release", TokenKind::ReleaseKeyword },
    { "repeat", TokenKind::RepeatKeyword },
    { "restrict", TokenKind::RestrictKeyword },
    { "return", TokenKind::ReturnKeyword },
    { "rnmos", TokenKind::RnmosKeyword },
    { "rpmos", TokenKind::RpmosKeyword },
    { "rtran", TokenKind::RtranKeyword },
    { "rtranif0", TokenKind::RtranIf0Keyword },
    { "rtranif1", TokenKind::RtranIf1Keyword },
    { "s_always", TokenKind::SAlwaysKeyword },
    { "s_eventually", TokenKind::SEventuallyKeyword },
    { "s_nexttime", TokenKind::SNextTimeKeyword },
    { "s_until", TokenKind::SUntilKeyword },
    { "s_until_with", TokenKind::SUntilWithKeyword },
    { "scalared", TokenKind::ScalaredKeyword },
    { "sequence", TokenKind::SequenceKeyword },
    { "shortint", TokenKind::ShortIntKeyword },
    { "shortreal", TokenKind::ShortRealKeyword },
    { "showcancelled", TokenKind::ShowCancelledKeyword },
    { "signed", TokenKind::SignedKeyword },
    { "small", TokenKind::SmallKeyword },
    { "soft", TokenKind::SoftKeyword },
    { "solve", TokenKind::SolveKeyword },
    { "specify", TokenKind::SpecifyKeyword },
    { "specparam", TokenKind::SpecParamKeyword },
    { "static", TokenKind::StaticKeyword },
    { "string", TokenKind::StringKeyword },
    { "strong", TokenKind::StrongKeyword },
    { "strong0", TokenKind::Strong0Keyword },
    { "strong1", TokenKind::Strong1Keyword },
    { "struct", TokenKind::StructKeyword },
    { "super", TokenKind::SuperKeyword },
    { "supply0", TokenKind::Supply0Keyword },
    { "supply1", TokenKind::Supply1Keyword },
    { "sync_accept_on", TokenKind::SyncAcceptOnKeyword },
    { "sync_reject_on", TokenKind::SyncRejectOnKeyword },
    { "table", TokenKind::TableKeyword },
    { "tagged", TokenKind::TaggedKeyword },
    { "task", TokenKind::TaskKeyword },
    { "this", TokenKind::ThisKeyword },
    { "throughout", TokenKind::ThroughoutKeyword },
    { "time", TokenKind::TimeKeyword },
    { "timeprecision", TokenKind::TimePrecisionKeyword },
    { "timeunit", TokenKind::TimeUnitKeyword },
    { "tran", TokenKind::TranKeyword },
    { "tranif0", TokenKind::TranIf0Keyword },
    { "tranif1", TokenKind::TranIf1Keyword },
    { "tri", TokenKind::TriKeyword },
    { "tri0", TokenKind::Tri0Keyword },
    { "tri1", TokenKind::Tri1Keyword },
    { "triand", TokenKind::TriAndKeyword },
    { "trior", TokenKind::TriOrKeyword },
    { "trireg", TokenKind::TriRegKeyword },
    { "type", TokenKind::TypeKeyword },
    { "typedef", TokenKind::TypedefKeyword },
    { "union", TokenKind::UnionKeyword },
    { "unique", TokenKind::UniqueKeyword },
    { "unique0", TokenKind::Unique0Keyword },
    { "unsigned", TokenKind::UnsignedKeyword },
    { "until", TokenKind::UntilKeyword },
    { "until_with", TokenKind::UntilWithKeyword },
    { "untyped", TokenKind::UntypedKeyword },
    { "use", TokenKind::UseKeyword },
    { "uwire", TokenKind::UWireKeyword },
    { "var", TokenKind::VarKeyword },
    { "vectored", TokenKind::VectoredKeyword },
    { "virtual", TokenKind::VirtualKeyword },
    { "void", TokenKind::VoidKeyword },
    { "wait", TokenKind::WaitKeyword },
    { "wait_order", TokenKind::WaitOrderKeyword },
    { "wand", TokenKind::WAndKeyword },
    { "weak", TokenKind::WeakKeyword },
    { "weak0", TokenKind::Weak0Keyword },
    { "weak1", TokenKind::Weak1Keyword },
    { "while", TokenKind::WhileKeyword },
    { "wildcard", TokenKind::WildcardKeyword },
    { "wire", TokenKind::WireKeyword },
    { "with", TokenKind::WithKeyword },
    { "within", TokenKind::WithinKeyword },
    { "wor", TokenKind::WOrKeyword },
    { "xor", TokenKind::XorKeyword },
    { "xnor", TokenKind::XnorKeyword }
};

TokenKind getSystemKeywordKind(StringRef text) {
    TokenKind kind;
    if (systemIdentifierKeywords.lookup(text, kind))
        return kind;
    return TokenKind::Unknown;
}

SyntaxKind getDirectiveKind(StringRef directive) {
    SyntaxKind kind;
    if (directiveTable.lookup(directive, kind))
        return kind;
    return SyntaxKind::MacroUsage;
}

const StringTable<TokenKind>* getKeywordTable() {
    return &allKeywords;
}

StringRef getDirectiveText(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::BeginKeywordsDirective: return "`begin_keywords";
        case SyntaxKind::CellDefineDirective: return "`celldefine";
        case SyntaxKind::DefaultNetTypeDirective: return "`default_nettype";
        case SyntaxKind::DefineDirective: return "`define";
        case SyntaxKind::ElseDirective: return "`else";
        case SyntaxKind::ElseIfDirective: return "`elseif";
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
        case SyntaxKind::TimescaleDirective: return "`timescale";
        case SyntaxKind::UnconnectedDriveDirective: return "`unconnected_drive";
        case SyntaxKind::UndefDirective: return "`undef";
        case SyntaxKind::UndefineAllDirective: return "`undefineall";
        default: return nullptr;
    }
}

StringRef getTokenKindText(TokenKind kind) {
    switch (kind) {
        // punctuation
        case TokenKind::Apostrophe: return "'";
        case TokenKind::ApostropheOpenBrace: return "'{";
        case TokenKind::OpenBrace: return "{";
        case TokenKind::CloseBrace: return "}";
        case TokenKind::OpenBracket: return "[";
        case TokenKind::CloseBracket: return "]";
        case TokenKind::OpenParenthesis: return "(";
        case TokenKind::OpenParenthesisStar: return "(*";
        case TokenKind::OpenParenthesisStarCloseParenthesis: return "(*)";
        case TokenKind::CloseParenthesis: return ")";
        case TokenKind::StarCloseParenthesis: return "*)";
        case TokenKind::Semicolon: return ";";
        case TokenKind::Colon: return ":";
        case TokenKind::ColonEquals: return ":=";
        case TokenKind::ColonSlash: return ":/";
        case TokenKind::DoubleColon: return "::";
        case TokenKind::StarDoubleColonStar: return "*::*";
        case TokenKind::Comma: return ",";
        case TokenKind::DotStar: return ".*";
        case TokenKind::Dot: return ".";
        case TokenKind::Slash: return "/";
        case TokenKind::Star: return "*";
        case TokenKind::DoubleStar: return "**";
        case TokenKind::StarArrow: return "*>";
        case TokenKind::Plus: return "+";
        case TokenKind::DoublePlus: return "++";
        case TokenKind::PlusColon: return "+:";
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
        case TokenKind::AtStar: return "@*";
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
        case TokenKind::MacroEscapedQuote: return "`\\`\"";
        case TokenKind::MacroPaste: return "``";

        default: return nullptr;
    }
}

std::ostream& operator<<(std::ostream& os, TokenKind kind) {
#define CASE(name) case TokenKind::name: os << #name; break
    switch (kind) {
        CASE(Unknown);
        CASE(EndOfFile);
        CASE(Identifier);
        CASE(SystemIdentifier);
        CASE(StringLiteral);
        CASE(IntegerLiteral);
        CASE(RealLiteral);
        CASE(TimeLiteral);
        CASE(Apostrophe);
        CASE(ApostropheOpenBrace);
        CASE(OpenBrace);
        CASE(CloseBrace);
        CASE(OpenBracket);
        CASE(CloseBracket);
        CASE(OpenParenthesis);
        CASE(OpenParenthesisStar);
        CASE(OpenParenthesisStarCloseParenthesis);
        CASE(CloseParenthesis);
        CASE(StarCloseParenthesis);
        CASE(Semicolon);
        CASE(Colon);
        CASE(ColonEquals);
        CASE(ColonSlash);
        CASE(DoubleColon);
        CASE(StarDoubleColonStar);
        CASE(Comma);
        CASE(DotStar);
        CASE(Dot);
        CASE(Slash);
        CASE(Star);
        CASE(DoubleStar);
        CASE(StarArrow);
        CASE(Plus);
        CASE(DoublePlus);
        CASE(PlusColon);
        CASE(Minus);
        CASE(DoubleMinus);
        CASE(MinusColon);
        CASE(MinusArrow);
        CASE(MinusDoubleArrow);
        CASE(Tilde);
        CASE(TildeAnd);
        CASE(TildeOr);
        CASE(TildeXor);
        CASE(Dollar);
        CASE(Question);
        CASE(Hash);
        CASE(DoubleHash);
        CASE(HashMinusHash);
        CASE(HashEqualsHash);
        CASE(Xor);
        CASE(XorTilde);
        CASE(Equals);
        CASE(DoubleEquals);
        CASE(DoubleEqualsQuestion);
        CASE(TripleEquals);
        CASE(EqualsArrow);
        CASE(PlusEqual);
        CASE(MinusEqual);
        CASE(SlashEqual);
        CASE(StarEqual);
        CASE(AndEqual);
        CASE(OrEqual);
        CASE(PercentEqual);
        CASE(XorEqual);
        CASE(LeftShiftEqual);
        CASE(TripleLeftShiftEqual);
        CASE(RightShiftEqual);
        CASE(TripleRightShiftEqual);
        CASE(LeftShift);
        CASE(RightShift);
        CASE(TripleLeftShift);
        CASE(TripleRightShift);
        CASE(Exclamation);
        CASE(ExclamationEquals);
        CASE(ExclamationEqualsQuestion);
        CASE(ExclamationDoubleEquals);
        CASE(Percent);
        CASE(LessThan);
        CASE(LessThanEquals);
        CASE(LessThanMinusArrow);
        CASE(GreaterThan);
        CASE(GreaterThanEquals);
        CASE(Or);
        CASE(DoubleOr);
        CASE(OrMinusArrow);
        CASE(OrEqualsArrow);
        CASE(At);
        CASE(AtStar);
        CASE(DoubleAt);
        CASE(And);
        CASE(DoubleAnd);
        CASE(TripleAnd);
        CASE(OneStep);
        CASE(AcceptOnKeyword);
        CASE(AliasKeyword);
        CASE(AlwaysKeyword);
        CASE(AlwaysCombKeyword);
        CASE(AlwaysFFKeyword);
        CASE(AlwaysLatchKeyword);
        CASE(AndKeyword);
        CASE(AssertKeyword);
        CASE(AssignKeyword);
        CASE(AssumeKeyword);
        CASE(AutomaticKeyword);
        CASE(BeforeKeyword);
        CASE(BeginKeyword);
        CASE(BindKeyword);
        CASE(BinsKeyword);
        CASE(BinsOfKeyword);
        CASE(BitKeyword);
        CASE(BreakKeyword);
        CASE(BufKeyword);
        CASE(BufIf0Keyword);
        CASE(BufIf1Keyword);
        CASE(ByteKeyword);
        CASE(CaseKeyword);
        CASE(CaseXKeyword);
        CASE(CaseZKeyword);
        CASE(CellKeyword);
        CASE(CHandleKeyword);
        CASE(CheckerKeyword);
        CASE(ClassKeyword);
        CASE(ClockingKeyword);
        CASE(CmosKeyword);
        CASE(ConfigKeyword);
        CASE(ConstKeyword);
        CASE(ConstraintKeyword);
        CASE(ContextKeyword);
        CASE(ContinueKeyword);
        CASE(CoverKeyword);
        CASE(CoverGroupKeyword);
        CASE(CoverPointKeyword);
        CASE(CrossKeyword);
        CASE(DeassignKeyword);
        CASE(DefaultKeyword);
        CASE(DefParamKeyword);
        CASE(DesignKeyword);
        CASE(DisableKeyword);
        CASE(DistKeyword);
        CASE(DoKeyword);
        CASE(EdgeKeyword);
        CASE(ElseKeyword);
        CASE(EndKeyword);
        CASE(EndCaseKeyword);
        CASE(EndCheckerKeyword);
        CASE(EndClassKeyword);
        CASE(EndClockingKeyword);
        CASE(EndConfigKeyword);
        CASE(EndFunctionKeyword);
        CASE(EndGenerateKeyword);
        CASE(EndGroupKeyword);
        CASE(EndInterfaceKeyword);
        CASE(EndModuleKeyword);
        CASE(EndPackageKeyword);
        CASE(EndPrimitiveKeyword);
        CASE(EndProgramKeyword);
        CASE(EndPropertyKeyword);
        CASE(EndSpecifyKeyword);
        CASE(EndSequenceKeyword);
        CASE(EndTableKeyword);
        CASE(EndTaskKeyword);
        CASE(EnumKeyword);
        CASE(EventKeyword);
        CASE(EventuallyKeyword);
        CASE(ExpectKeyword);
        CASE(ExportKeyword);
        CASE(ExtendsKeyword);
        CASE(ExternKeyword);
        CASE(FinalKeyword);
        CASE(FirstMatchKeyword);
        CASE(ForKeyword);
        CASE(ForceKeyword);
        CASE(ForeachKeyword);
        CASE(ForeverKeyword);
        CASE(ForkKeyword);
        CASE(ForkJoinKeyword);
        CASE(FunctionKeyword);
        CASE(GenerateKeyword);
        CASE(GenVarKeyword);
        CASE(GlobalKeyword);
        CASE(HighZ0Keyword);
        CASE(HighZ1Keyword);
        CASE(IfKeyword);
        CASE(IffKeyword);
        CASE(IfNoneKeyword);
        CASE(IgnoreBinsKeyword);
        CASE(IllegalBinsKeyword);
        CASE(ImplementsKeyword);
        CASE(ImpliesKeyword);
        CASE(ImportKeyword);
        CASE(IncDirKeyword);
        CASE(IncludeKeyword);
        CASE(InitialKeyword);
        CASE(InOutKeyword);
        CASE(InputKeyword);
        CASE(InsideKeyword);
        CASE(InstanceKeyword);
        CASE(IntKeyword);
        CASE(IntegerKeyword);
        CASE(InterconnectKeyword);
        CASE(InterfaceKeyword);
        CASE(IntersectKeyword);
        CASE(JoinKeyword);
        CASE(JoinAnyKeyword);
        CASE(JoinNoneKeyword);
        CASE(LargeKeyword);
        CASE(LetKeyword);
        CASE(LibListKeyword);
        CASE(LibraryKeyword);
        CASE(LocalKeyword);
        CASE(LocalParamKeyword);
        CASE(LogicKeyword);
        CASE(LongIntKeyword);
        CASE(MacromoduleKeyword);
        CASE(MatchesKeyword);
        CASE(MediumKeyword);
        CASE(ModPortKeyword);
        CASE(ModuleKeyword);
        CASE(NandKeyword);
        CASE(NegEdgeKeyword);
        CASE(NetTypeKeyword);
        CASE(NewKeyword);
        CASE(NextTimeKeyword);
        CASE(NmosKeyword);
        CASE(NorKeyword);
        CASE(NoShowCancelledKeyword);
        CASE(NotKeyword);
        CASE(NotIf0Keyword);
        CASE(NotIf1Keyword);
        CASE(NullKeyword);
        CASE(OrKeyword);
        CASE(OutputKeyword);
        CASE(PackageKeyword);
        CASE(PackedKeyword);
        CASE(ParameterKeyword);
        CASE(PmosKeyword);
        CASE(PosEdgeKeyword);
        CASE(PrimitiveKeyword);
        CASE(PriorityKeyword);
        CASE(ProgramKeyword);
        CASE(PropertyKeyword);
        CASE(ProtectedKeyword);
        CASE(Pull0Keyword);
        CASE(Pull1Keyword);
        CASE(PullDownKeyword);
        CASE(PullUpKeyword);
        CASE(PulseStyleOnDetectKeyword);
        CASE(PulseStyleOnEventKeyword);
        CASE(PureKeyword);
        CASE(RandKeyword);
        CASE(RandCKeyword);
        CASE(RandCaseKeyword);
        CASE(RandSequenceKeyword);
        CASE(RcmosKeyword);
        CASE(RealKeyword);
        CASE(RealTimeKeyword);
        CASE(RefKeyword);
        CASE(RegKeyword);
        CASE(RejectOnKeyword);
        CASE(ReleaseKeyword);
        CASE(RepeatKeyword);
        CASE(RestrictKeyword);
        CASE(ReturnKeyword);
        CASE(RnmosKeyword);
        CASE(RpmosKeyword);
        CASE(RtranKeyword);
        CASE(RtranIf0Keyword);
        CASE(RtranIf1Keyword);
        CASE(SAlwaysKeyword);
        CASE(SEventuallyKeyword);
        CASE(SNextTimeKeyword);
        CASE(SUntilKeyword);
        CASE(SUntilWithKeyword);
        CASE(ScalaredKeyword);
        CASE(SequenceKeyword);
        CASE(ShortIntKeyword);
        CASE(ShortRealKeyword);
        CASE(ShowCancelledKeyword);
        CASE(SignedKeyword);
        CASE(SmallKeyword);
        CASE(SoftKeyword);
        CASE(SolveKeyword);
        CASE(SpecifyKeyword);
        CASE(SpecParamKeyword);
        CASE(StaticKeyword);
        CASE(StringKeyword);
        CASE(StrongKeyword);
        CASE(Strong0Keyword);
        CASE(Strong1Keyword);
        CASE(StructKeyword);
        CASE(SuperKeyword);
        CASE(Supply0Keyword);
        CASE(Supply1Keyword);
        CASE(SyncAcceptOnKeyword);
        CASE(SyncRejectOnKeyword);
        CASE(TableKeyword);
        CASE(TaggedKeyword);
        CASE(TaskKeyword);
        CASE(ThisKeyword);
        CASE(ThroughoutKeyword);
        CASE(TimeKeyword);
        CASE(TimePrecisionKeyword);
        CASE(TimeUnitKeyword);
        CASE(TranKeyword);
        CASE(TranIf0Keyword);
        CASE(TranIf1Keyword);
        CASE(TriKeyword);
        CASE(Tri0Keyword);
        CASE(Tri1Keyword);
        CASE(TriAndKeyword);
        CASE(TriOrKeyword);
        CASE(TriRegKeyword);
        CASE(TypeKeyword);
        CASE(TypedefKeyword);
        CASE(UnionKeyword);
        CASE(UniqueKeyword);
        CASE(Unique0Keyword);
        CASE(UnsignedKeyword);
        CASE(UntilKeyword);
        CASE(UntilWithKeyword);
        CASE(UntypedKeyword);
        CASE(UseKeyword);
        CASE(UWireKeyword);
        CASE(VarKeyword);
        CASE(VectoredKeyword);
        CASE(VirtualKeyword);
        CASE(VoidKeyword);
        CASE(WaitKeyword);
        CASE(WaitOrderKeyword);
        CASE(WAndKeyword);
        CASE(WeakKeyword);
        CASE(Weak0Keyword);
        CASE(Weak1Keyword);
        CASE(WhileKeyword);
        CASE(WildcardKeyword);
        CASE(WireKeyword);
        CASE(WithKeyword);
        CASE(WithinKeyword);
        CASE(WOrKeyword);
        CASE(XnorKeyword);
        CASE(XorKeyword);
        CASE(UnitSystemName);
        CASE(RootSystemName);
        CASE(Directive);
        CASE(EndOfDirective);
        CASE(IncludeFileName);
        CASE(MacroUsage);
        CASE(MacroQuote);
        CASE(MacroEscapedQuote);
        CASE(MacroPaste);
        default: ASSERT(false && "Missing case");
    }
    return os;
#undef CASE
}

std::ostream& operator<<(std::ostream& os, TriviaKind kind) {
#define CASE(name) case TriviaKind::name: os << #name; break
    switch (kind) {
        CASE(Unknown);
        CASE(Whitespace);
        CASE(EndOfLine);
        CASE(LineContinuation);
        CASE(LineComment);
        CASE(BlockComment);
        CASE(DisabledText);
        CASE(SkippedTokens);
        CASE(Directive);
        default: ASSERT(false && "Missing case");
    }
    return os;
#undef CASE
}

}
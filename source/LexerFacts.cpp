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
        case TokenKind::ApostropheOpenBrace: return "'{";
        case TokenKind::OpenBrace: return "{";
        case TokenKind::CloseBrace: return "}";
        case TokenKind::OpenBracket: return "[";
        case TokenKind::CloseBracket: return "]";
        case TokenKind::OpenParenthesis: return "(";
        case TokenKind::OpenParenthesisStar: return "(*";
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
        case TokenKind::DoubleAt: return "@@";
        case TokenKind::And: return "&";
        case TokenKind::DoubleAnd: return "&&";
        case TokenKind::TripleAnd: return "&&&";

            // keywords
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
    switch (kind) {
        case TokenKind::Unknown: os << "Unknown"; break;
        case TokenKind::EndOfFile: os << "EndOfFile"; break;
        case TokenKind::Identifier: os << "Identifier"; break;
        case TokenKind::SystemIdentifier: os << "SystemIdentifier"; break;
        case TokenKind::StringLiteral: os << "StringLiteral"; break;
        case TokenKind::IntegerLiteral: os << "IntegerLiteral"; break;
        case TokenKind::RealLiteral: os << "RealLiteral"; break;
        case TokenKind::TimeLiteral: os << "TimeLiteral"; break;
        case TokenKind::ApostropheOpenBrace: os << "ApostropheOpenBrace"; break;
        case TokenKind::OpenBrace: os << "OpenBrace"; break;
        case TokenKind::CloseBrace: os << "CloseBrace"; break;
        case TokenKind::OpenBracket: os << "OpenBracket"; break;
        case TokenKind::CloseBracket: os << "CloseBracket"; break;
        case TokenKind::OpenParenthesis: os << "OpenParenthesis"; break;
        case TokenKind::OpenParenthesisStar: os << "OpenParenthesisStar"; break;
        case TokenKind::CloseParenthesis: os << "CloseParenthesis"; break;
        case TokenKind::StarCloseParenthesis: os << "StarCloseParenthesis"; break;
        case TokenKind::Semicolon: os << "Semicolon"; break;
        case TokenKind::Colon: os << "Colon"; break;
        case TokenKind::ColonEquals: os << "ColonEquals"; break;
        case TokenKind::ColonSlash: os << "ColonSlash"; break;
        case TokenKind::DoubleColon: os << "DoubleColon"; break;
        case TokenKind::StarDoubleColonStar: os << "StarDoubleColonStar"; break;
        case TokenKind::Comma: os << "Comma"; break;
        case TokenKind::DotStar: os << "DotStar"; break;
        case TokenKind::Dot: os << "Dot"; break;
        case TokenKind::Slash: os << "Slash"; break;
        case TokenKind::Star: os << "Star"; break;
        case TokenKind::DoubleStar: os << "DoubleStar"; break;
        case TokenKind::StarArrow: os << "StarArrow"; break;
        case TokenKind::Plus: os << "Plus"; break;
        case TokenKind::DoublePlus: os << "DoublePlus"; break;
        case TokenKind::PlusColon: os << "PlusColon"; break;
        case TokenKind::Minus: os << "Minus"; break;
        case TokenKind::DoubleMinus: os << "DoubleMinus"; break;
        case TokenKind::MinusColon: os << "MinusColon"; break;
        case TokenKind::MinusArrow: os << "MinusArrow"; break;
        case TokenKind::MinusDoubleArrow: os << "MinusDoubleArrow"; break;
        case TokenKind::Tilde: os << "Tilde"; break;
        case TokenKind::TildeAnd: os << "TildeAnd"; break;
        case TokenKind::TildeOr: os << "TildeOr"; break;
        case TokenKind::TildeXor: os << "TildeXor"; break;
        case TokenKind::Dollar: os << "Dollar"; break;
        case TokenKind::Question: os << "Question"; break;
        case TokenKind::Hash: os << "Hash"; break;
        case TokenKind::DoubleHash: os << "DoubleHash"; break;
        case TokenKind::HashMinusHash: os << "HashMinusHash"; break;
        case TokenKind::HashEqualsHash: os << "HashEqualsHash"; break;
        case TokenKind::Xor: os << "Xor"; break;
        case TokenKind::XorTilde: os << "XorTilde"; break;
        case TokenKind::Equals: os << "Equals"; break;
        case TokenKind::DoubleEquals: os << "DoubleEquals"; break;
        case TokenKind::DoubleEqualsQuestion: os << "DoubleEqualsQuestion"; break;
        case TokenKind::TripleEquals: os << "TripleEquals"; break;
        case TokenKind::EqualsArrow: os << "EqualsArrow"; break;
        case TokenKind::PlusEqual: os << "PlusEqual"; break;
        case TokenKind::MinusEqual: os << "MinusEqual"; break;
        case TokenKind::SlashEqual: os << "SlashEqual"; break;
        case TokenKind::StarEqual: os << "StarEqual"; break;
        case TokenKind::AndEqual: os << "AndEqual"; break;
        case TokenKind::OrEqual: os << "OrEqual"; break;
        case TokenKind::PercentEqual: os << "PercentEqual"; break;
        case TokenKind::XorEqual: os << "XorEqual"; break;
        case TokenKind::LeftShiftEqual: os << "LeftShiftEqual"; break;
        case TokenKind::TripleLeftShiftEqual: os << "TripleLeftShiftEqual"; break;
        case TokenKind::RightShiftEqual: os << "RightShiftEqual"; break;
        case TokenKind::TripleRightShiftEqual: os << "TripleRightShiftEqual"; break;
        case TokenKind::LeftShift: os << "LeftShift"; break;
        case TokenKind::RightShift: os << "RightShift"; break;
        case TokenKind::TripleLeftShift: os << "TripleLeftShift"; break;
        case TokenKind::TripleRightShift: os << "TripleRightShift"; break;
        case TokenKind::Exclamation: os << "Exclamation"; break;
        case TokenKind::ExclamationEquals: os << "ExclamationEquals"; break;
        case TokenKind::ExclamationEqualsQuestion: os << "ExclamationEqualsQuestion"; break;
        case TokenKind::ExclamationDoubleEquals: os << "ExclamationDoubleEquals"; break;
        case TokenKind::Percent: os << "Percent"; break;
        case TokenKind::LessThan: os << "LessThan"; break;
        case TokenKind::LessThanEquals: os << "LessThanEquals"; break;
        case TokenKind::LessThanMinusArrow: os << "LessThanMinusArrow"; break;
        case TokenKind::GreaterThan: os << "GreaterThan"; break;
        case TokenKind::GreaterThanEquals: os << "GreaterThanEquals"; break;
        case TokenKind::Or: os << "Or"; break;
        case TokenKind::DoubleOr: os << "DoubleOr"; break;
        case TokenKind::OrMinusArrow: os << "OrMinusArrow"; break;
        case TokenKind::OrEqualsArrow: os << "OrEqualsArrow"; break;
        case TokenKind::At: os << "At"; break;
        case TokenKind::DoubleAt: os << "DoubleAt"; break;
        case TokenKind::And: os << "And"; break;
        case TokenKind::DoubleAnd: os << "DoubleAnd"; break;
        case TokenKind::TripleAnd: os << "TripleAnd"; break;
        case TokenKind::AcceptOnKeyword: os << "AcceptOnKeyword"; break;
        case TokenKind::AliasKeyword: os << "AliasKeyword"; break;
        case TokenKind::AlwaysKeyword: os << "AlwaysKeyword"; break;
        case TokenKind::AlwaysCombKeyword: os << "AlwaysCombKeyword"; break;
        case TokenKind::AlwaysFFKeyword: os << "AlwaysFFKeyword"; break;
        case TokenKind::AlwaysLatchKeyword: os << "AlwaysLatchKeyword"; break;
        case TokenKind::AndKeyword: os << "AndKeyword"; break;
        case TokenKind::AssertKeyword: os << "AssertKeyword"; break;
        case TokenKind::AssignKeyword: os << "AssignKeyword"; break;
        case TokenKind::AssumeKeyword: os << "AssumeKeyword"; break;
        case TokenKind::AutomaticKeyword: os << "AutomaticKeyword"; break;
        case TokenKind::BeforeKeyword: os << "BeforeKeyword"; break;
        case TokenKind::BeginKeyword: os << "BeginKeyword"; break;
        case TokenKind::BindKeyword: os << "BindKeyword"; break;
        case TokenKind::BinsKeyword: os << "BinsKeyword"; break;
        case TokenKind::BinsOfKeyword: os << "BinsOfKeyword"; break;
        case TokenKind::BitKeyword: os << "BitKeyword"; break;
        case TokenKind::BreakKeyword: os << "BreakKeyword"; break;
        case TokenKind::BufKeyword: os << "BufKeyword"; break;
        case TokenKind::BufIf0Keyword: os << "BufIf0Keyword"; break;
        case TokenKind::BufIf1Keyword: os << "BufIf1Keyword"; break;
        case TokenKind::ByteKeyword: os << "ByteKeyword"; break;
        case TokenKind::CaseKeyword: os << "CaseKeyword"; break;
        case TokenKind::CaseXKeyword: os << "CaseXKeyword"; break;
        case TokenKind::CaseZKeyword: os << "CaseZKeyword"; break;
        case TokenKind::CellKeyword: os << "CellKeyword"; break;
        case TokenKind::CHandleKeyword: os << "CHandleKeyword"; break;
        case TokenKind::CheckerKeyword: os << "CheckerKeyword"; break;
        case TokenKind::ClassKeyword: os << "ClassKeyword"; break;
        case TokenKind::ClockingKeyword: os << "ClockingKeyword"; break;
        case TokenKind::CmosKeyword: os << "CmosKeyword"; break;
        case TokenKind::ConfigKeyword: os << "ConfigKeyword"; break;
        case TokenKind::ConstKeyword: os << "ConstKeyword"; break;
        case TokenKind::ConstraintKeyword: os << "ConstraintKeyword"; break;
        case TokenKind::ContextKeyword: os << "ContextKeyword"; break;
        case TokenKind::ContinueKeyword: os << "ContinueKeyword"; break;
        case TokenKind::CoverKeyword: os << "CoverKeyword"; break;
        case TokenKind::CoverGroupKeyword: os << "CoverGroupKeyword"; break;
        case TokenKind::CoverPointKeyword: os << "CoverPointKeyword"; break;
        case TokenKind::CrossKeyword: os << "CrossKeyword"; break;
        case TokenKind::DeassignKeyword: os << "DeassignKeyword"; break;
        case TokenKind::DefaultKeyword: os << "DefaultKeyword"; break;
        case TokenKind::DefParamKeyword: os << "DefParamKeyword"; break;
        case TokenKind::DesignKeyword: os << "DesignKeyword"; break;
        case TokenKind::DisableKeyword: os << "DisableKeyword"; break;
        case TokenKind::DistKeyword: os << "DistKeyword"; break;
        case TokenKind::DoKeyword: os << "DoKeyword"; break;
        case TokenKind::EdgeKeyword: os << "EdgeKeyword"; break;
        case TokenKind::ElseKeyword: os << "ElseKeyword"; break;
        case TokenKind::EndKeyword: os << "EndKeyword"; break;
        case TokenKind::EndCaseKeyword: os << "EndCaseKeyword"; break;
        case TokenKind::EndCheckerKeyword: os << "EndCheckerKeyword"; break;
        case TokenKind::EndClassKeyword: os << "EndClassKeyword"; break;
        case TokenKind::EndClockingKeyword: os << "EndClockingKeyword"; break;
        case TokenKind::EndConfigKeyword: os << "EndConfigKeyword"; break;
        case TokenKind::EndFunctionKeyword: os << "EndFunctionKeyword"; break;
        case TokenKind::EndGenerateKeyword: os << "EndGenerateKeyword"; break;
        case TokenKind::EndGroupKeyword: os << "EndGroupKeyword"; break;
        case TokenKind::EndInterfaceKeyword: os << "EndInterfaceKeyword"; break;
        case TokenKind::EndModuleKeyword: os << "EndModuleKeyword"; break;
        case TokenKind::EndPackageKeyword: os << "EndPackageKeyword"; break;
        case TokenKind::EndPrimitiveKeyword: os << "EndPrimitiveKeyword"; break;
        case TokenKind::EndProgramKeyword: os << "EndProgramKeyword"; break;
        case TokenKind::EndPropertyKeyword: os << "EndPropertyKeyword"; break;
        case TokenKind::EndSpecifyKeyword: os << "EndSpecifyKeyword"; break;
        case TokenKind::EndSequenceKeyword: os << "EndSequenceKeyword"; break;
        case TokenKind::EndTableKeyword: os << "EndTableKeyword"; break;
        case TokenKind::EndTaskKeyword: os << "EndTaskKeyword"; break;
        case TokenKind::EnumKeyword: os << "EnumKeyword"; break;
        case TokenKind::EventKeyword: os << "EventKeyword"; break;
        case TokenKind::EventuallyKeyword: os << "EventuallyKeyword"; break;
        case TokenKind::ExpectKeyword: os << "ExpectKeyword"; break;
        case TokenKind::ExportKeyword: os << "ExportKeyword"; break;
        case TokenKind::ExtendsKeyword: os << "ExtendsKeyword"; break;
        case TokenKind::ExternKeyword: os << "ExternKeyword"; break;
        case TokenKind::FinalKeyword: os << "FinalKeyword"; break;
        case TokenKind::FirstMatchKeyword: os << "FirstMatchKeyword"; break;
        case TokenKind::ForKeyword: os << "ForKeyword"; break;
        case TokenKind::ForceKeyword: os << "ForceKeyword"; break;
        case TokenKind::ForeachKeyword: os << "ForeachKeyword"; break;
        case TokenKind::ForeverKeyword: os << "ForeverKeyword"; break;
        case TokenKind::ForkKeyword: os << "ForkKeyword"; break;
        case TokenKind::ForkJoinKeyword: os << "ForkJoinKeyword"; break;
        case TokenKind::FunctionKeyword: os << "FunctionKeyword"; break;
        case TokenKind::GenerateKeyword: os << "GenerateKeyword"; break;
        case TokenKind::GenVarKeyword: os << "GenVarKeyword"; break;
        case TokenKind::GlobalKeyword: os << "GlobalKeyword"; break;
        case TokenKind::HighZ0Keyword: os << "HighZ0Keyword"; break;
        case TokenKind::HighZ1Keyword: os << "HighZ1Keyword"; break;
        case TokenKind::IfKeyword: os << "IfKeyword"; break;
        case TokenKind::IffKeyword: os << "IffKeyword"; break;
        case TokenKind::IfNoneKeyword: os << "IfNoneKeyword"; break;
        case TokenKind::IgnoreBinsKeyword: os << "IgnoreBinsKeyword"; break;
        case TokenKind::IllegalBinsKeyword: os << "IllegalBinsKeyword"; break;
        case TokenKind::ImplementsKeyword: os << "ImplementsKeyword"; break;
        case TokenKind::ImpliesKeyword: os << "ImpliesKeyword"; break;
        case TokenKind::ImportKeyword: os << "ImportKeyword"; break;
        case TokenKind::IncDirKeyword: os << "IncDirKeyword"; break;
        case TokenKind::IncludeKeyword: os << "IncludeKeyword"; break;
        case TokenKind::InitialKeyword: os << "InitialKeyword"; break;
        case TokenKind::InOutKeyword: os << "InOutKeyword"; break;
        case TokenKind::InputKeyword: os << "InputKeyword"; break;
        case TokenKind::InsideKeyword: os << "InsideKeyword"; break;
        case TokenKind::InstanceKeyword: os << "InstanceKeyword"; break;
        case TokenKind::IntKeyword: os << "IntKeyword"; break;
        case TokenKind::IntegerKeyword: os << "IntegerKeyword"; break;
        case TokenKind::InterconnectKeyword: os << "InterconnectKeyword"; break;
        case TokenKind::InterfaceKeyword: os << "InterfaceKeyword"; break;
        case TokenKind::IntersectKeyword: os << "IntersectKeyword"; break;
        case TokenKind::JoinKeyword: os << "JoinKeyword"; break;
        case TokenKind::JoinAnyKeyword: os << "JoinAnyKeyword"; break;
        case TokenKind::JoinNoneKeyword: os << "JoinNoneKeyword"; break;
        case TokenKind::LargeKeyword: os << "LargeKeyword"; break;
        case TokenKind::LetKeyword: os << "LetKeyword"; break;
        case TokenKind::LibListKeyword: os << "LibListKeyword"; break;
        case TokenKind::LibraryKeyword: os << "LibraryKeyword"; break;
        case TokenKind::LocalKeyword: os << "LocalKeyword"; break;
        case TokenKind::LocalParamKeyword: os << "LocalParamKeyword"; break;
        case TokenKind::LogicKeyword: os << "LogicKeyword"; break;
        case TokenKind::LongIntKeyword: os << "LongIntKeyword"; break;
        case TokenKind::MacromoduleKeyword: os << "MacromoduleKeyword"; break;
        case TokenKind::MatchesKeyword: os << "MatchesKeyword"; break;
        case TokenKind::MediumKeyword: os << "MediumKeyword"; break;
        case TokenKind::ModPortKeyword: os << "ModPortKeyword"; break;
        case TokenKind::ModuleKeyword: os << "ModuleKeyword"; break;
        case TokenKind::NandKeyword: os << "NandKeyword"; break;
        case TokenKind::NegEdgeKeyword: os << "NegEdgeKeyword"; break;
        case TokenKind::NetTypeKeyword: os << "NetTypeKeyword"; break;
        case TokenKind::NewKeyword: os << "NewKeyword"; break;
        case TokenKind::NextTimeKeyword: os << "NextTimeKeyword"; break;
        case TokenKind::NmosKeyword: os << "NmosKeyword"; break;
        case TokenKind::NorKeyword: os << "NorKeyword"; break;
        case TokenKind::NoShowCancelledKeyword: os << "NoShowCancelledKeyword"; break;
        case TokenKind::NotKeyword: os << "NotKeyword"; break;
        case TokenKind::NotIf0Keyword: os << "NotIf0Keyword"; break;
        case TokenKind::NotIf1Keyword: os << "NotIf1Keyword"; break;
        case TokenKind::NullKeyword: os << "NullKeyword"; break;
        case TokenKind::OrKeyword: os << "OrKeyword"; break;
        case TokenKind::OutputKeyword: os << "OutputKeyword"; break;
        case TokenKind::PackageKeyword: os << "PackageKeyword"; break;
        case TokenKind::PackedKeyword: os << "PackedKeyword"; break;
        case TokenKind::ParameterKeyword: os << "ParameterKeyword"; break;
        case TokenKind::PmosKeyword: os << "PmosKeyword"; break;
        case TokenKind::PosEdgeKeyword: os << "PosEdgeKeyword"; break;
        case TokenKind::PrimitiveKeyword: os << "PrimitiveKeyword"; break;
        case TokenKind::PriorityKeyword: os << "PriorityKeyword"; break;
        case TokenKind::ProgramKeyword: os << "ProgramKeyword"; break;
        case TokenKind::PropertyKeyword: os << "PropertyKeyword"; break;
        case TokenKind::ProtectedKeyword: os << "ProtectedKeyword"; break;
        case TokenKind::Pull0Keyword: os << "Pull0Keyword"; break;
        case TokenKind::Pull1Keyword: os << "Pull1Keyword"; break;
        case TokenKind::PullDownKeyword: os << "PullDownKeyword"; break;
        case TokenKind::PullUpKeyword: os << "PullUpKeyword"; break;
        case TokenKind::PulseStyleOnDetectKeyword: os << "PulseStyleOnDetectKeyword"; break;
        case TokenKind::PulseStyleOnEventKeyword: os << "PulseStyleOnEventKeyword"; break;
        case TokenKind::PureKeyword: os << "PureKeyword"; break;
        case TokenKind::RandKeyword: os << "RandKeyword"; break;
        case TokenKind::RandCKeyword: os << "RandCKeyword"; break;
        case TokenKind::RandCaseKeyword: os << "RandCaseKeyword"; break;
        case TokenKind::RandSequenceKeyword: os << "RandSequenceKeyword"; break;
        case TokenKind::RcmosKeyword: os << "RcmosKeyword"; break;
        case TokenKind::RealKeyword: os << "RealKeyword"; break;
        case TokenKind::RealTimeKeyword: os << "RealTimeKeyword"; break;
        case TokenKind::RefKeyword: os << "RefKeyword"; break;
        case TokenKind::RegKeyword: os << "RegKeyword"; break;
        case TokenKind::RejectOnKeyword: os << "RejectOnKeyword"; break;
        case TokenKind::ReleaseKeyword: os << "ReleaseKeyword"; break;
        case TokenKind::RepeatKeyword: os << "RepeatKeyword"; break;
        case TokenKind::RestrictKeyword: os << "RestrictKeyword"; break;
        case TokenKind::ReturnKeyword: os << "ReturnKeyword"; break;
        case TokenKind::RnmosKeyword: os << "RnmosKeyword"; break;
        case TokenKind::RpmosKeyword: os << "RpmosKeyword"; break;
        case TokenKind::RtranKeyword: os << "RtranKeyword"; break;
        case TokenKind::RtranIf0Keyword: os << "RtranIf0Keyword"; break;
        case TokenKind::RtranIf1Keyword: os << "RtranIf1Keyword"; break;
        case TokenKind::SAlwaysKeyword: os << "SAlwaysKeyword"; break;
        case TokenKind::SEventuallyKeyword: os << "SEventuallyKeyword"; break;
        case TokenKind::SNextTimeKeyword: os << "SNextTimeKeyword"; break;
        case TokenKind::SUntilKeyword: os << "SUntilKeyword"; break;
        case TokenKind::SUntilWithKeyword: os << "SUntilWithKeyword"; break;
        case TokenKind::ScalaredKeyword: os << "ScalaredKeyword"; break;
        case TokenKind::SequenceKeyword: os << "SequenceKeyword"; break;
        case TokenKind::ShortIntKeyword: os << "ShortIntKeyword"; break;
        case TokenKind::ShortRealKeyword: os << "ShortRealKeyword"; break;
        case TokenKind::ShowCancelledKeyword: os << "ShowCancelledKeyword"; break;
        case TokenKind::SignedKeyword: os << "SignedKeyword"; break;
        case TokenKind::SmallKeyword: os << "SmallKeyword"; break;
        case TokenKind::SoftKeyword: os << "SoftKeyword"; break;
        case TokenKind::SolveKeyword: os << "SolveKeyword"; break;
        case TokenKind::SpecifyKeyword: os << "SpecifyKeyword"; break;
        case TokenKind::SpecParamKeyword: os << "SpecParamKeyword"; break;
        case TokenKind::StaticKeyword: os << "StaticKeyword"; break;
        case TokenKind::StringKeyword: os << "StringKeyword"; break;
        case TokenKind::StrongKeyword: os << "StrongKeyword"; break;
        case TokenKind::Strong0Keyword: os << "Strong0Keyword"; break;
        case TokenKind::Strong1Keyword: os << "Strong1Keyword"; break;
        case TokenKind::StructKeyword: os << "StructKeyword"; break;
        case TokenKind::SuperKeyword: os << "SuperKeyword"; break;
        case TokenKind::Supply0Keyword: os << "Supply0Keyword"; break;
        case TokenKind::Supply1Keyword: os << "Supply1Keyword"; break;
        case TokenKind::SyncAcceptOnKeyword: os << "SyncAcceptOnKeyword"; break;
        case TokenKind::SyncRejectOnKeyword: os << "SyncRejectOnKeyword"; break;
        case TokenKind::TableKeyword: os << "TableKeyword"; break;
        case TokenKind::TaggedKeyword: os << "TaggedKeyword"; break;
        case TokenKind::TaskKeyword: os << "TaskKeyword"; break;
        case TokenKind::ThisKeyword: os << "ThisKeyword"; break;
        case TokenKind::ThroughoutKeyword: os << "ThroughoutKeyword"; break;
        case TokenKind::TimeKeyword: os << "TimeKeyword"; break;
        case TokenKind::TimePrecisionKeyword: os << "TimePrecisionKeyword"; break;
        case TokenKind::TimeUnitKeyword: os << "TimeUnitKeyword"; break;
        case TokenKind::TranKeyword: os << "TranKeyword"; break;
        case TokenKind::TranIf0Keyword: os << "TranIf0Keyword"; break;
        case TokenKind::TranIf1Keyword: os << "TranIf1Keyword"; break;
        case TokenKind::TriKeyword: os << "TriKeyword"; break;
        case TokenKind::Tri0Keyword: os << "Tri0Keyword"; break;
        case TokenKind::Tri1Keyword: os << "Tri1Keyword"; break;
        case TokenKind::TriAndKeyword: os << "TriAndKeyword"; break;
        case TokenKind::TriOrKeyword: os << "TriOrKeyword"; break;
        case TokenKind::TriRegKeyword: os << "TriRegKeyword"; break;
        case TokenKind::TypeKeyword: os << "TypeKeyword"; break;
        case TokenKind::TypedefKeyword: os << "TypedefKeyword"; break;
        case TokenKind::UnionKeyword: os << "UnionKeyword"; break;
        case TokenKind::UniqueKeyword: os << "UniqueKeyword"; break;
        case TokenKind::Unique0Keyword: os << "Unique0Keyword"; break;
        case TokenKind::UnsignedKeyword: os << "UnsignedKeyword"; break;
        case TokenKind::UntilKeyword: os << "UntilKeyword"; break;
        case TokenKind::UntilWithKeyword: os << "UntilWithKeyword"; break;
        case TokenKind::UntypedKeyword: os << "UntypedKeyword"; break;
        case TokenKind::UseKeyword: os << "UseKeyword"; break;
        case TokenKind::UWireKeyword: os << "UWireKeyword"; break;
        case TokenKind::VarKeyword: os << "VarKeyword"; break;
        case TokenKind::VectoredKeyword: os << "VectoredKeyword"; break;
        case TokenKind::VirtualKeyword: os << "VirtualKeyword"; break;
        case TokenKind::VoidKeyword: os << "VoidKeyword"; break;
        case TokenKind::WaitKeyword: os << "WaitKeyword"; break;
        case TokenKind::WaitOrderKeyword: os << "WaitOrderKeyword"; break;
        case TokenKind::WAndKeyword: os << "WAndKeyword"; break;
        case TokenKind::WeakKeyword: os << "WeakKeyword"; break;
        case TokenKind::Weak0Keyword: os << "Weak0Keyword"; break;
        case TokenKind::Weak1Keyword: os << "Weak1Keyword"; break;
        case TokenKind::WhileKeyword: os << "WhileKeyword"; break;
        case TokenKind::WildcardKeyword: os << "WildcardKeyword"; break;
        case TokenKind::WireKeyword: os << "WireKeyword"; break;
        case TokenKind::WithKeyword: os << "WithKeyword"; break;
        case TokenKind::WithinKeyword: os << "WithinKeyword"; break;
        case TokenKind::WOrKeyword: os << "WOrKeyword"; break;
        case TokenKind::XnorKeyword: os << "XnorKeyword"; break;
        case TokenKind::XorKeyword: os << "XorKeyword"; break;
        case TokenKind::UnitSystemName: os << "UnitSystemName"; break;
        case TokenKind::RootSystemName: os << "RootSystemName"; break;
        case TokenKind::Directive: os << "Directive"; break;
        case TokenKind::EndOfDirective: os << "EndOfDirective"; break;
        case TokenKind::IncludeFileName: os << "IncludeFileName"; break;
        case TokenKind::MacroUsage: os << "MacroUsage"; break;
        case TokenKind::MacroQuote: os << "MacroQuote"; break;
        case TokenKind::MacroEscapedQuote: os << "MacroEscapedQuote"; break;
        case TokenKind::MacroPaste: os << "MacroPaste"; break;
        default: os << "<unknown>"; break;
    }
    return os;
}

std::ostream& operator<<(std::ostream& os, TriviaKind kind) {
    switch (kind) {
        case TriviaKind::Unknown: os << "Unknown"; break;
        case TriviaKind::Whitespace: os << "Whitespace"; break;
        case TriviaKind::EndOfLine: os << "EndOfLine"; break;
        case TriviaKind::LineContinuation: os << "LineContinuation"; break;
        case TriviaKind::LineComment: os << "LineComment"; break;
        case TriviaKind::BlockComment: os << "BlockComment"; break;
        case TriviaKind::DisabledText: os << "DisabledText"; break;
        case TriviaKind::SkippedTokens: os << "SkippedTokens"; break;
        default: os << "<unknown>"; break;
    }
    return os;
}

}
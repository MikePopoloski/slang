//------------------------------------------------------------------------------
// Token.h
// Contains Token class and related helpers.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/SVInt.h"
#include "slang/numeric/Time.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"
#include "slang/util/StringTable.h"
#include "slang/util/Util.h"

namespace slang {

enum class SyntaxKind;
enum class TokenKind : uint16_t;

class Diagnostics;
class SyntaxNode;
class Token;

/// Various flags that we track on the token.
enum class TokenFlags : uint8_t { None = 0, Missing = 1 };
BITMASK_DEFINE_MAX_ELEMENT(TokenFlags, Missing);

/// Various flags for numeric tokens.
struct NumericTokenFlags {
    uint8_t raw = 0;

    LiteralBase base() const { return LiteralBase(raw & 0b11); }
    bool isSigned() const { return (raw & 0b100) != 0; }
    TimeUnit unit() const { return TimeUnit((raw & 0b111000) >> 3); }
    bool outOfRange() const { return (raw & 0b1000000) != 0; }

    void set(LiteralBase base, bool isSigned);
    void set(TimeUnit unit);
    void setOutOfRange(bool value);
};

/// The original kind of identifier represented by a token.
enum class IdentifierType : uint8_t { Unknown, Normal, Escaped, System };

/// The kind of trivia we've stored.
enum class TriviaKind : uint8_t {
    Unknown,
    Whitespace,
    EndOfLine,
    LineComment,
    BlockComment,
    DisabledText,
    SkippedTokens,
    SkippedSyntax,
    Directive
};

/// The Trivia class holds on to a piece of source text that should otherwise
/// not turn into a token; for example, a preprocessor directive, a line continuation
/// character, or a comment.
class Trivia {
private:
#pragma pack(push, 4)
    struct ShortStringView {
        const char* ptr;
        uint32_t len;
    };
    struct ShortTokenSpan {
        const Token* ptr;
        uint32_t len;
    };
    struct FullLocation {
        string_view text;
        SourceLocation location;
    };

    union {
        ShortStringView rawText;
        ShortTokenSpan tokens;
        SyntaxNode* syntaxNode;
        FullLocation* fullLocation;
    };
#pragma pack(pop)

    // The vast majority of trivia lives alongside the token it's attached to, so if
    // you want to know its source location just walk backward from the parent location.
    // For certain cases though (the preprocessor inserted tokens) the trivia gets glued
    // together from different locations. In that case hasFullLocation will be true and
    // the union will point at a FullLocation structure.
    bool hasFullLocation = false;

public:
    TriviaKind kind;

    Trivia();
    Trivia(TriviaKind kind, string_view rawText);
    Trivia(TriviaKind kind, span<Token const> tokens);
    Trivia(TriviaKind kind, SyntaxNode* syntax);

    /// If the trivia is raw source text, creates a new trivia with the specified location
    /// (instead of implicitly offset from the parent token). If this trivia is for a
    /// directive or skipped tokens, returns a copy without modification.
    [[nodiscard]] Trivia withLocation(BumpAllocator& alloc, SourceLocation location) const;

    /// Gets the source location of the trivia if one is explicitly known. If not, nullopt
    /// is returned to signify that the location is implicitly relative to the parent token.
    optional<SourceLocation> getExplicitLocation() const;

    /// If this trivia is tracking a skipped syntax node or a directive, returns that node.
    /// Otherwise returns nullptr.
    SyntaxNode* syntax() const;

    /// Get the raw text of the trivia, if any.
    string_view getRawText() const;

    /// If the trivia represents skipped tokens, returns the list of tokens that were
    /// skipped. Otherwise returns an empty span.
    span<Token const> getSkippedTokens() const;
};
static_assert(sizeof(Trivia) == 16);

/// Represents a single lexed token, including leading trivia, original location, token kind,
/// and any related information derived from the token itself (such as the lexeme).
///
/// This class is a lightweight immutable structure designed to be copied around and stored
/// wherever. The bulk of the token's data is stored in a heap allocated block. Most of the
/// hot path only cares about the token's kind, so that's given priority.
class Token {
public:
    /// Heap-allocated info block.
    struct Info {
        /// Numeric-related information.
        struct NumericLiteralInfo {
            std::variant<logic_t, double, SVIntStorage> value;
            NumericTokenFlags numericFlags;
        };

        /// Leading trivia.
        span<slang::Trivia const> trivia;

        /// The raw source span.
        string_view rawText;

        /// The original location in the source text (or a macro location
        /// if the token was generated during macro expansion).
        SourceLocation location;

        /// Extra kind-specific data associated with the token.
        /// string_view: The nice text of a string literal.
        /// SyntaxKind: The kind of a directive token.
        /// IdentifierType: The kind of an identifer token.
        /// NumericLiteralInfo: Info for numeric tokens.
        std::variant<string_view, SyntaxKind, IdentifierType, NumericLiteralInfo> extra;

        /// Various token flags.
        bitmask<TokenFlags> flags;

        Info() = default;
        Info(span<Trivia const> trivia, string_view rawText, SourceLocation location,
             bitmask<TokenFlags> flags = TokenFlags::None);

        void setBit(logic_t value);
        void setReal(double value, bool outOfRange);
        void setInt(BumpAllocator& alloc, const SVInt& value);
        void setNumFlags(LiteralBase base, bool isSigned);
        void setTimeUnit(TimeUnit unit);

        const string_view& stringText() const { return std::get<string_view>(extra); }
        const SyntaxKind& directiveKind() const { return std::get<SyntaxKind>(extra); }
        const IdentifierType& idType() const { return std::get<IdentifierType>(extra); }
        const NumericLiteralInfo& numInfo() const { return std::get<NumericLiteralInfo>(extra); }
    };

    /// The kind of the token; this is not in the info block because
    /// we almost always want to look at it (perf).
    TokenKind kind;

    Token();
    Token(TokenKind kind, const Info* info);

    /// A missing token was expected and inserted by the parser at a given point.
    bool isMissing() const { return (info->flags & TokenFlags::Missing) != 0; }

    SourceRange range() const;
    SourceLocation location() const { return info->location; }
    span<Trivia const> trivia() const { return info->trivia; }
    const Info* getInfo() const { return info; }

    /// Value text is the "nice" lexed version of certain tokens;
    /// for example, in string literals, escape sequences are converted appropriately.
    string_view valueText() const;

    /// Gets the original lexeme that led to the creation of this token.
    string_view rawText() const;

    /// Prints the token (including all of its trivia) to a string.
    std::string toString() const;

    /// Data accessors for specific kinds of tokens.
    /// These will generally assert if the kind is wrong.
    SVInt intValue() const;
    double realValue() const;
    logic_t bitValue() const;
    NumericTokenFlags numericFlags() const;
    IdentifierType identifierType() const;
    SyntaxKind directiveKind() const;

    bool valid() const { return info != nullptr; }
    explicit operator bool() const { return valid(); }

    /// Modification methods to make it easier to deal with immutable tokens.
    [[nodiscard]] Token withTrivia(BumpAllocator& alloc, span<Trivia const> trivia) const;
    [[nodiscard]] Token withLocation(BumpAllocator& alloc, SourceLocation location) const;

    static Token createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location);
    static Token createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual,
                                TokenKind expected, Token lastConsumed);

private:
    const Info* info;
};

static_assert(std::is_trivially_copyable_v<Token>);

/// Different restricted sets of keywords that can be set using the
/// `begin_keywords directive. The values of the enum correspond to indexes to
/// allKeywords[] in LexerFacts.cpp
enum class KeywordVersion : uint8_t {
    v1364_1995 = 0,
    v1364_2001_noconfig = 1,
    v1364_2001 = 2,
    v1364_2005 = 3,
    v1800_2005 = 4,
    v1800_2009 = 5,
    v1800_2012 = 6,
    v1800_2017 = 7,
};

TokenKind getSystemKeywordKind(string_view text);
string_view getTokenKindText(TokenKind kind);
KeywordVersion getDefaultKeywordVersion();
optional<KeywordVersion> getKeywordVersion(string_view text);
const StringTable<TokenKind>* getKeywordTable(KeywordVersion version);

/// This checks all keywords, regardless of the current keyword table.  Should
/// only be used when it is ok to get a false positive for a keyword that may
/// not currently be in the keyword table (such as handling macro arguments).
bool isKeyword(TokenKind kind);

enum class TokenKind : uint16_t {
    // general
    Unknown,
    EndOfFile,
    Identifier,
    StringLiteral,
    IntegerLiteral,
    IntegerBase,
    UnbasedUnsizedLiteral,
    RealLiteral,
    TimeLiteral,

    // punctuation
    Apostrophe,
    ApostropheOpenBrace,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    OpenParenthesis,
    OpenParenthesisStar,
    CloseParenthesis,
    StarCloseParenthesis,
    Semicolon,
    Colon,
    ColonEquals,
    ColonSlash,
    DoubleColon,
    StarDoubleColonStar,
    Comma,
    DotStar,
    Dot,
    Slash,
    Star,
    DoubleStar,
    StarArrow,
    Plus,
    DoublePlus,
    PlusColon,
    Minus,
    DoubleMinus,
    MinusColon,
    MinusArrow,
    MinusDoubleArrow,
    Tilde,
    TildeAnd,
    TildeOr,
    TildeXor,
    Dollar,
    Question,
    Hash,
    DoubleHash,
    HashMinusHash,
    HashEqualsHash,
    Xor,
    XorTilde,
    Equals,
    DoubleEquals,
    DoubleEqualsQuestion,
    TripleEquals,
    EqualsArrow,
    PlusEqual,
    MinusEqual,
    SlashEqual,
    StarEqual,
    AndEqual,
    OrEqual,
    PercentEqual,
    XorEqual,
    LeftShiftEqual,
    TripleLeftShiftEqual,
    RightShiftEqual,
    TripleRightShiftEqual,
    LeftShift,
    RightShift,
    TripleLeftShift,
    TripleRightShift,
    Exclamation,
    ExclamationEquals,
    ExclamationEqualsQuestion,
    ExclamationDoubleEquals,
    Percent,
    LessThan,
    LessThanEquals,
    LessThanMinusArrow,
    GreaterThan,
    GreaterThanEquals,
    Or,
    DoubleOr,
    OrMinusArrow,
    OrMinusDoubleArrow,
    OrEqualsArrow,
    At,
    DoubleAt,
    And,
    DoubleAnd,
    TripleAnd,

    // keywords
    OneStep,
    AcceptOnKeyword,
    AliasKeyword,
    AlwaysKeyword,
    AlwaysCombKeyword,
    AlwaysFFKeyword,
    AlwaysLatchKeyword,
    AndKeyword,
    AssertKeyword,
    AssignKeyword,
    AssumeKeyword,
    AutomaticKeyword,
    BeforeKeyword,
    BeginKeyword,
    BindKeyword,
    BinsKeyword,
    BinsOfKeyword,
    BitKeyword,
    BreakKeyword,
    BufKeyword,
    BufIf0Keyword,
    BufIf1Keyword,
    ByteKeyword,
    CaseKeyword,
    CaseXKeyword,
    CaseZKeyword,
    CellKeyword,
    CHandleKeyword,
    CheckerKeyword,
    ClassKeyword,
    ClockingKeyword,
    CmosKeyword,
    ConfigKeyword,
    ConstKeyword,
    ConstraintKeyword,
    ContextKeyword,
    ContinueKeyword,
    CoverKeyword,
    CoverGroupKeyword,
    CoverPointKeyword,
    CrossKeyword,
    DeassignKeyword,
    DefaultKeyword,
    DefParamKeyword,
    DesignKeyword,
    DisableKeyword,
    DistKeyword,
    DoKeyword,
    EdgeKeyword,
    ElseKeyword,
    EndKeyword,
    EndCaseKeyword,
    EndCheckerKeyword,
    EndClassKeyword,
    EndClockingKeyword,
    EndConfigKeyword,
    EndFunctionKeyword,
    EndGenerateKeyword,
    EndGroupKeyword,
    EndInterfaceKeyword,
    EndModuleKeyword,
    EndPackageKeyword,
    EndPrimitiveKeyword,
    EndProgramKeyword,
    EndPropertyKeyword,
    EndSpecifyKeyword,
    EndSequenceKeyword,
    EndTableKeyword,
    EndTaskKeyword,
    EnumKeyword,
    EventKeyword,
    EventuallyKeyword,
    ExpectKeyword,
    ExportKeyword,
    ExtendsKeyword,
    ExternKeyword,
    FinalKeyword,
    FirstMatchKeyword,
    ForKeyword,
    ForceKeyword,
    ForeachKeyword,
    ForeverKeyword,
    ForkKeyword,
    ForkJoinKeyword,
    FunctionKeyword,
    GenerateKeyword,
    GenVarKeyword,
    GlobalKeyword,
    HighZ0Keyword,
    HighZ1Keyword,
    IfKeyword,
    IffKeyword,
    IfNoneKeyword,
    IgnoreBinsKeyword,
    IllegalBinsKeyword,
    ImplementsKeyword,
    ImpliesKeyword,
    ImportKeyword,
    IncDirKeyword,
    IncludeKeyword,
    InitialKeyword,
    InOutKeyword,
    InputKeyword,
    InsideKeyword,
    InstanceKeyword,
    IntKeyword,
    IntegerKeyword,
    InterconnectKeyword,
    InterfaceKeyword,
    IntersectKeyword,
    JoinKeyword,
    JoinAnyKeyword,
    JoinNoneKeyword,
    LargeKeyword,
    LetKeyword,
    LibListKeyword,
    LibraryKeyword,
    LocalKeyword,
    LocalParamKeyword,
    LogicKeyword,
    LongIntKeyword,
    MacromoduleKeyword,
    MatchesKeyword,
    MediumKeyword,
    ModPortKeyword,
    ModuleKeyword,
    NandKeyword,
    NegEdgeKeyword,
    NetTypeKeyword,
    NewKeyword,
    NextTimeKeyword,
    NmosKeyword,
    NorKeyword,
    NoShowCancelledKeyword,
    NotKeyword,
    NotIf0Keyword,
    NotIf1Keyword,
    NullKeyword,
    OrKeyword,
    OutputKeyword,
    PackageKeyword,
    PackedKeyword,
    ParameterKeyword,
    PmosKeyword,
    PosEdgeKeyword,
    PrimitiveKeyword,
    PriorityKeyword,
    ProgramKeyword,
    PropertyKeyword,
    ProtectedKeyword,
    Pull0Keyword,
    Pull1Keyword,
    PullDownKeyword,
    PullUpKeyword,
    PulseStyleOnDetectKeyword,
    PulseStyleOnEventKeyword,
    PureKeyword,
    RandKeyword,
    RandCKeyword,
    RandCaseKeyword,
    RandSequenceKeyword,
    RcmosKeyword,
    RealKeyword,
    RealTimeKeyword,
    RefKeyword,
    RegKeyword,
    RejectOnKeyword,
    ReleaseKeyword,
    RepeatKeyword,
    RestrictKeyword,
    ReturnKeyword,
    RnmosKeyword,
    RpmosKeyword,
    RtranKeyword,
    RtranIf0Keyword,
    RtranIf1Keyword,
    SAlwaysKeyword,
    SEventuallyKeyword,
    SNextTimeKeyword,
    SUntilKeyword,
    SUntilWithKeyword,
    ScalaredKeyword,
    SequenceKeyword,
    ShortIntKeyword,
    ShortRealKeyword,
    ShowCancelledKeyword,
    SignedKeyword,
    SmallKeyword,
    SoftKeyword,
    SolveKeyword,
    SpecifyKeyword,
    SpecParamKeyword,
    StaticKeyword,
    StringKeyword,
    StrongKeyword,
    Strong0Keyword,
    Strong1Keyword,
    StructKeyword,
    SuperKeyword,
    Supply0Keyword,
    Supply1Keyword,
    SyncAcceptOnKeyword,
    SyncRejectOnKeyword,
    TableKeyword,
    TaggedKeyword,
    TaskKeyword,
    ThisKeyword,
    ThroughoutKeyword,
    TimeKeyword,
    TimePrecisionKeyword,
    TimeUnitKeyword,
    TranKeyword,
    TranIf0Keyword,
    TranIf1Keyword,
    TriKeyword,
    Tri0Keyword,
    Tri1Keyword,
    TriAndKeyword,
    TriOrKeyword,
    TriRegKeyword,
    TypeKeyword,
    TypedefKeyword,
    UnionKeyword,
    UniqueKeyword,
    Unique0Keyword,
    UnsignedKeyword,
    UntilKeyword,
    UntilWithKeyword,
    UntypedKeyword,
    UseKeyword,
    UWireKeyword,
    VarKeyword,
    VectoredKeyword,
    VirtualKeyword,
    VoidKeyword,
    WaitKeyword,
    WaitOrderKeyword,
    WAndKeyword,
    WeakKeyword,
    Weak0Keyword,
    Weak1Keyword,
    WhileKeyword,
    WildcardKeyword,
    WireKeyword,
    WithKeyword,
    WithinKeyword,
    WOrKeyword,
    XnorKeyword,
    XorKeyword,

    // predefined system keywords
    UnitSystemName,
    RootSystemName,

    // directives (these get consumed by the preprocessor and don't make it downstream to the
    // parser)
    Directive,
    IncludeFileName,
    MacroUsage,
    MacroQuote,
    MacroEscapedQuote,
    MacroPaste,
    EmptyMacroArgument,
    LineContinuation
};

} // namespace slang

#pragma once

#include "ArrayRef.h"
#include "Buffer.h"
#include "BitVector.h"
#include "Trivia.h"

namespace slang {

enum class TokenKind : uint16_t;

enum class IdentifierType : uint8_t {
    Unknown,
    Normal,
    Escaped,
    System
};

struct IdentifierInfo {
    StringRef rawText;
    IdentifierType type;

    IdentifierInfo(StringRef rawText, IdentifierType type) :
        rawText(rawText), type(type) {
    }
};

struct StringLiteralInfo {
    StringRef rawText;
    StringRef niceText;

    StringLiteralInfo(StringRef rawText, StringRef niceText) :
        rawText(rawText), niceText(niceText) {
    }
};

struct NumericValue {
    union {
        logic_t bit;
        int32_t integer;
        double real;
        LogicVector vector;
    };

    uint8_t type;

    NumericValue(double real) : type(Real), real(real) {}
    NumericValue(int32_t integer) : type(SignedInteger), integer(integer) {}
    NumericValue(logic_t bit) : type(UnsizedBit), bit(bit) {}
    NumericValue(LogicVector vector) : type(Vector), vector(vector) {}

    enum {
        Real,
        SignedInteger,
        Vector,
        UnsizedBit
    };
};

struct NumericLiteralInfo {
    StringRef rawText;
    NumericValue value;

    NumericLiteralInfo(StringRef rawText, NumericValue value) :
        rawText(rawText), value(value) {
    }
};

struct DirectiveInfo {
    StringRef rawText;
    TriviaKind kind;

    DirectiveInfo(StringRef rawText, TriviaKind kind) :
        rawText(rawText), kind(kind) {
    }
};

class Token {
public:
    ArrayRef<Trivia> trivia;
    TokenKind kind;

    Token(TokenKind kind, void* data, ArrayRef<Trivia> trivia)
        : kind(kind),
          data(data),
          trivia(trivia) {
    }

    // value text is the "nice" lexed version of certain tokens;
    // for example, in string literals, escape sequences are converted appropriately
    StringRef valueText() const;

    // convenience methods that wrap writeTo
    // toFullString() includes trivia, toString() does not
    std::string toString() const;
    std::string toFullString() const;

    // copy string representation to the given buffer
    void writeTo(Buffer<char>& buffer, bool includeTrivia) const;

    // data accessors for specific kinds of tokens
    // these will generally assert if the kind is wrong
    const NumericValue& numericValue() const;
    IdentifierType identifierType() const;
    TriviaKind directiveKind() const;

    // gets the opaque extended data pointer
    // should only be used to copy to a new Token
    void* getDataPtr() const { return data; }

private:
    union {
        void* data;
        IdentifierInfo* identifier;
        StringLiteralInfo* string;
        NumericLiteralInfo* numeric;
        DirectiveInfo* directive;
    };

    enum {
        StartOfLine,
        IsMissing
    };
};

std::ostream& operator<<(std::ostream& os, TokenKind kind);

enum class TokenKind : uint16_t {
    // general
    Unknown,
    EndOfFile,
    Identifier,
    SystemIdentifier,
    StringLiteral,
    IntegerLiteral,
    RealLiteral,
    TimeLiteral,

    // punctuation
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
    OrEqualsArrow,
    At,
    DoubleAt,
    And,
    DoubleAnd,
    TripleAnd,

    // keywords
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

    // directives (these get consumed by the preprocessor and don't make it downstream to the parser)
    Directive,
    EndOfDirective,
    UserIncludeFileName,
    SystemIncludeFileName,
    MacroUsage,
    MacroQuote,
    MacroEscapedQuote,
    MacroPaste
};

}
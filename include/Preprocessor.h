#pragma once

namespace slang {

class Preprocessor {

};

enum class DirectiveType : uint8_t {
    Unknown,
    ResetAll,
    Include,
    Define,
    Undef,
    UndefineAll,
    Ifdef,
    Ifndef,
    Else,
    Elseif,
    Endif,
    Timescale,
    DefaultNetType,
    UnconnectedDrive,
    NoUnconnectedDrive,
    CellDefine,
    EndCellDefine,
    Pragma,
    SetLine,
    GetFile,
    GetLine,
    BeginKeywords,
    EndKeywords
};

}
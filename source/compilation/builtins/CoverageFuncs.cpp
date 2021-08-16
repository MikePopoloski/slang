//------------------------------------------------------------------------------
// CoverageFuncs.cpp
// Coverage control functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class CoverageControlFunc : public SimpleSystemSubroutine {
public:
    CoverageControlFunc(Compilation& comp) : SimpleSystemSubroutine("$coverage_control", SubroutineKind::Function, 4,
       { &comp.getIntType(), &comp.getIntType(), &comp.getIntType(), &comp.getStringType() }, comp.getIntType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class CoverageGetMaxFunc : public SimpleSystemSubroutine {
public:
    CoverageGetMaxFunc(Compilation& comp) : SimpleSystemSubroutine("$coverage_get_max", SubroutineKind::Function, 3,
       { &comp.getIntType(), &comp.getIntType(), &comp.getStringType() }, comp.getIntType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class CoverageGet : public SimpleSystemSubroutine {
public:
    CoverageGet(Compilation& comp) : SimpleSystemSubroutine("$coverage_get", SubroutineKind::Function, 3,
       { &comp.getIntType(), &comp.getIntType(), &comp.getStringType() }, comp.getIntType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class CoverageMerge : public SimpleSystemSubroutine {
public:
    CoverageMerge(Compilation& comp) : SimpleSystemSubroutine("$coverage_merge", SubroutineKind::Function, 2,
       { &comp.getIntType(), &comp.getStringType() }, comp.getIntType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class CoverageSave : public SimpleSystemSubroutine {
public:
    CoverageSave(Compilation& comp) : SimpleSystemSubroutine("$coverage_save", SubroutineKind::Function, 2,
       { &comp.getIntType(), &comp.getStringType() }, comp.getIntType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class GetCoverage : public SimpleSystemSubroutine {
public:
    GetCoverage(Compilation& comp) : SimpleSystemSubroutine("$get_coverage", SubroutineKind::Function, 0,
        {}, comp.getRealType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class SetCoverageDbName : public SimpleSystemSubroutine {
public:
    SetCoverageDbName(Compilation& comp) : SimpleSystemSubroutine("$set_coverage_db_name", SubroutineKind::Function, 1,
        { &comp.getStringType() }, comp.getVoidType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

class LoadCoverageDb : public SimpleSystemSubroutine {
public:
    LoadCoverageDb(Compilation& comp) : SimpleSystemSubroutine("$load_coverage_db", SubroutineKind::Function, 1,
        { &comp.getStringType() }, comp.getVoidType(), false) {};

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }
};

void registerCoverageFuncs(Compilation& c) {
#define REGISTER(name, ...) \
    c.addSystemSubroutine(std::make_unique<name>(__VA_ARGS__))
    REGISTER(CoverageControlFunc, c);
    REGISTER(CoverageGetMaxFunc, c);
    REGISTER(CoverageGet, c);
    REGISTER(CoverageMerge, c);
    REGISTER(CoverageSave, c);
    REGISTER(GetCoverage, c);
    REGISTER(SetCoverageDbName, c);
    REGISTER(LoadCoverageDb, c);
#undef REGISTER
}

} // namespace slang::Builtins

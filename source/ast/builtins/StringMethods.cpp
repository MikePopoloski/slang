//------------------------------------------------------------------------------
// StringMethods.cpp
// Built-in methods on strings
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/util/String.h"

namespace slang::ast::builtins {

class StringLenMethod : public SimpleSystemSubroutine {
public:
    explicit StringLenMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("len", SubroutineKind::Function, 0, {}, builtins.intType, true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, val.str().length(), true);
    }
};

class StringPutcMethod : public SimpleSystemSubroutine {
public:
    explicit StringPutcMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("putc", SubroutineKind::Function, 2,
                               {&builtins.intType, &builtins.byteType}, builtins.voidType, true,
                               /* isFirstArgLValue */ true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto strCv = args[0]->evalLValue(context);
        auto indexCv = args[1]->eval(context);
        auto charCv = args[2]->eval(context);
        if (!strCv || !indexCv || !charCv)
            return nullptr;

        const std::string& str = strCv.load().str();
        int32_t index = indexCv.integer().as<int32_t>().value();
        uint8_t c = charCv.integer().as<uint8_t>().value();

        if (c == 0 || index < 0 || size_t(index) >= str.length())
            return nullptr;

        strCv.addIndex(index, nullptr);
        strCv.store(SVInt(8, c, false));
        return nullptr;
    }
};

class StringGetcMethod : public SimpleSystemSubroutine {
public:
    explicit StringGetcMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("getc", SubroutineKind::Function, 1, {&builtins.intType},
                               builtins.byteType, true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto strCv = args[0]->eval(context);
        auto indexCv = args[1]->eval(context);
        if (!strCv || !indexCv)
            return nullptr;

        const std::string& str = strCv.str();
        int32_t index = indexCv.integer().as<int32_t>().value();
        if (index < 0 || size_t(index) >= str.length())
            return SVInt(8, 0, false);

        return SVInt(8, uint64_t(str[size_t(index)]), false);
    }
};

class StringUpperLowerMethod : public SimpleSystemSubroutine {
public:
    StringUpperLowerMethod(const Builtins& builtins, const std::string& name, bool upper) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, builtins.stringType, true),
        upper(upper) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        std::string& str = val.str();
        if (upper)
            strToUpper(str);
        else
            strToLower(str);
        return val;
    }

private:
    bool upper;
};

class StringCompareMethod : public SimpleSystemSubroutine {
public:
    StringCompareMethod(const Builtins& builtins, const std::string& name, bool ignoreCase) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 1, {&builtins.stringType},
                               builtins.intType, true),
        ignoreCase(ignoreCase) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lhsCv = args[0]->eval(context);
        auto rhsCv = args[1]->eval(context);
        if (!lhsCv || !rhsCv)
            return nullptr;

        std::string& lhs = lhsCv.str();
        std::string& rhs = rhsCv.str();

        int result;
        if (ignoreCase) {
            // No convenient way to do this with standard lib functions :(
            const char* p1 = lhs.c_str();
            const char* p2 = rhs.c_str();
            while ((result = charToLower(*p1) - charToLower(*p2++)) == 0) {
                if (*p1++ == '\0')
                    break;
            }
        }
        else {
            result = lhs.compare(rhs);
            if (result < 0)
                result = -1;
            else if (result > 0)
                result = 1;
        }

        return SVInt(32, uint64_t(result), true);
    }

private:
    bool ignoreCase;
};

class StringSubstrMethod : public SimpleSystemSubroutine {
public:
    explicit StringSubstrMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("substr", SubroutineKind::Function, 2,
                               {&builtins.intType, &builtins.intType}, builtins.stringType, true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto strCv = args[0]->eval(context);
        auto leftCv = args[1]->eval(context);
        auto rightCv = args[2]->eval(context);
        if (!strCv || !leftCv || !rightCv)
            return nullptr;

        const std::string& str = strCv.str();
        int32_t left = leftCv.integer().as<int32_t>().value();
        int32_t right = rightCv.integer().as<int32_t>().value();
        if (left < 0 || right < left || size_t(right) >= str.length())
            return ""s;

        int32_t count = right - left + 1;
        return str.substr(size_t(left), size_t(count));
    }
};

class StringAtoIMethod : public SimpleSystemSubroutine {
public:
    StringAtoIMethod(const Builtins& builtins, const std::string& name, int base) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, builtins.integerType, true),
        base(base) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto cv = args[0]->eval(context);
        if (!cv)
            return nullptr;

        std::string str = cv.str();
        std::erase(str, '_');

        int result = strToInt(str, nullptr, base).value_or(0);
        return SVInt(32, uint64_t(result), true);
    }

private:
    int base;
};

class StringAtoRealMethod : public SimpleSystemSubroutine {
public:
    explicit StringAtoRealMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("atoreal", SubroutineKind::Function, 0, {}, builtins.realType,
                               true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto cv = args[0]->eval(context);
        if (!cv)
            return nullptr;

        std::string str = cv.str();
        std::erase(str, '_');

        double result = strToDouble(str).value_or(0.0);
        return real_t(result);
    }
};

class StringItoAMethod : public SimpleSystemSubroutine {
public:
    StringItoAMethod(const Builtins& builtins, const std::string& name, LiteralBase base) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 1, {&builtins.integerType},
                               builtins.voidType, true, /* isFirstArgLValue */ true),
        base(base) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto strCv = args[0]->evalLValue(context);
        auto valCv = args[1]->eval(context);
        if (!strCv || !valCv)
            return nullptr;

        strCv.store(valCv.integer().toString(base, false));
        return nullptr;
    }

private:
    LiteralBase base;
};

class StringRealtoAMethod : public SimpleSystemSubroutine {
public:
    explicit StringRealtoAMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("realtoa", SubroutineKind::Function, 1, {&builtins.realType},
                               builtins.voidType, true, /* isFirstArgLValue */ true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto strCv = args[0]->evalLValue(context);
        auto valCv = args[1]->eval(context);
        if (!strCv || !valCv)
            return nullptr;

        strCv.store(std::to_string(valCv.real()));
        return nullptr;
    }
};

void Builtins::registerStringMethods() {
#define REGISTER(kind, name, ...) addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::StringType, StringLen, *this);
    REGISTER(SymbolKind::StringType, StringPutc, *this);
    REGISTER(SymbolKind::StringType, StringGetc, *this);
    REGISTER(SymbolKind::StringType, StringUpperLower, *this, "toupper", true);
    REGISTER(SymbolKind::StringType, StringUpperLower, *this, "tolower", false);
    REGISTER(SymbolKind::StringType, StringCompare, *this, "compare", false);
    REGISTER(SymbolKind::StringType, StringCompare, *this, "icompare", true);
    REGISTER(SymbolKind::StringType, StringSubstr, *this);
    REGISTER(SymbolKind::StringType, StringAtoI, *this, "atoi", 10);
    REGISTER(SymbolKind::StringType, StringAtoI, *this, "atohex", 16);
    REGISTER(SymbolKind::StringType, StringAtoI, *this, "atooct", 8);
    REGISTER(SymbolKind::StringType, StringAtoI, *this, "atobin", 2);
    REGISTER(SymbolKind::StringType, StringAtoReal, *this);
    REGISTER(SymbolKind::StringType, StringItoA, *this, "itoa", LiteralBase::Decimal);
    REGISTER(SymbolKind::StringType, StringItoA, *this, "hextoa", LiteralBase::Hex);
    REGISTER(SymbolKind::StringType, StringItoA, *this, "octtoa", LiteralBase::Octal);
    REGISTER(SymbolKind::StringType, StringItoA, *this, "bintoa", LiteralBase::Binary);
    REGISTER(SymbolKind::StringType, StringRealtoA, *this);

#undef REGISTER
}

} // namespace slang::ast::builtins

#pragma once

#include <ostream>

#include "slang/ast/types/Type.h"

namespace CppType {
enum Type { BOOL, U32, U64, SC_BV, STRUCT, ENUM };

std::string toString(const Type cppType);
Type fromSize(size_t size);
} // namespace CppType

class SvType {
public:
    explicit SvType(const slang::ast::Type& type);
    explicit SvType(const slang::ast::Type& type, std::string_view name) : SvType(type) {
        this->name = name;
    }

    inline bool isStruct() const { return cppType == CppType::STRUCT; }
    inline bool isEnum() const { return cppType == CppType::ENUM; }
    inline bool isStructOrEnum() const { return this->isStruct() || this->isEnum(); }

    std::string toString() const;
    friend std::ostream& operator<<(std::ostream& os, const SvType& type);

    CppType::Type cppType;
    size_t size;
    // It will only contain useful data if the cppType is either a struct or an enum
    std::string_view name;
    std::string_view _namespace;
};

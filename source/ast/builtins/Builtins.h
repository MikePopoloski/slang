//------------------------------------------------------------------------------
// Builtins.h
// Container type for canonical instance of various built-in types and methods
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <memory>
#include <string_view>
#include <tuple>

#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/util/FlatMap.h"

namespace slang::ast::builtins {

class Builtins {
public:
    ScalarType bitType{ScalarType::Bit};
    ScalarType logicType{ScalarType::Logic};
    ScalarType regType{ScalarType::Reg};
    ScalarType signedBitType{ScalarType::Bit, true};
    ScalarType signedLogicType{ScalarType::Logic, true};
    ScalarType signedRegType{ScalarType::Reg, true};
    PredefinedIntegerType intType{PredefinedIntegerType::Int};
    PredefinedIntegerType uintType{PredefinedIntegerType::Int, false};
    PredefinedIntegerType byteType{PredefinedIntegerType::Byte};
    PredefinedIntegerType integerType{PredefinedIntegerType::Integer};
    PredefinedIntegerType shortIntType{PredefinedIntegerType::ShortInt};
    PredefinedIntegerType longIntType{PredefinedIntegerType::LongInt};
    PredefinedIntegerType ulongIntType{PredefinedIntegerType::LongInt, false};
    PredefinedIntegerType timeType{PredefinedIntegerType::Time};
    FloatingType realType{FloatingType::Real};
    FloatingType shortRealType{FloatingType::ShortReal};
    FloatingType realTimeType{FloatingType::RealTime};
    StringType stringType;
    VoidType voidType;
    CHandleType chandleType;
    NullType nullType;
    EventType eventType;
    UnboundedType unboundedType;
    TypeRefType typeRefType;
    UntypedType untypedType;
    SequenceType sequenceType;
    PropertyType propertyType;

    // A table to look up scalar types based on combinations of the three flags: signed, fourstate,
    // reg. Two of the entries are not valid and will be nullptr (!fourstate & reg).
    Type* scalarTypeTable[8]{nullptr};

    std::vector<std::shared_ptr<SystemSubroutine>> systemSubroutines;
    flat_hash_map<std::string_view, std::shared_ptr<SystemSubroutine>> subroutineNameMap;
    flat_hash_map<std::tuple<std::string_view, SymbolKind>, std::shared_ptr<SystemSubroutine>>
        methodMap;

    static Builtins Instance;

    Builtins() {
        // Scalar types are indexed by bit flags.
        auto registerScalar = [this](auto& type) {
            scalarTypeTable[type.getIntegralFlags().bits() & 0x7] = &type;
        };
        registerScalar(bitType);
        registerScalar(logicType);
        registerScalar(regType);
        registerScalar(signedBitType);
        registerScalar(signedLogicType);
        registerScalar(signedRegType);

        systemSubroutines.resize(parsing::KnownSystemName_traits::values.size());

        registerArrayMethods();
        registerConversionFuncs();
        registerCoverageFuncs();
        registerEnumMethods();
        registerMathFuncs();
        registerMiscSystemFuncs();
        registerNonConstFuncs();
        registerQueryFuncs();
        registerStringMethods();
        registerSystemTasks();
    }

private:
    using KnownSystemName = parsing::KnownSystemName;

    void registerArrayMethods();
    void registerConversionFuncs();
    void registerCoverageFuncs();
    void registerEnumMethods();
    void registerMathFuncs();
    void registerMiscSystemFuncs();
    void registerNonConstFuncs();
    void registerQueryFuncs();
    void registerStringMethods();
    void registerSystemTasks();

    void addSystemSubroutine(std::shared_ptr<SystemSubroutine> subroutine) {
        SLANG_ASSERT(subroutine->knownNameId != KnownSystemName::Unknown);
        SLANG_ASSERT(!systemSubroutines[(size_t)subroutine->knownNameId]);
        subroutineNameMap.emplace(subroutine->name, subroutine);
        systemSubroutines[(size_t)subroutine->knownNameId] = std::move(subroutine);
    }

    void addSystemMethod(SymbolKind typeKind, std::shared_ptr<SystemSubroutine> method) {
        methodMap.emplace(std::make_tuple(std::string_view(method->name), typeKind),
                          std::move(method));
    }
};

} // namespace slang::ast::builtins

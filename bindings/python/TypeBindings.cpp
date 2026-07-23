//------------------------------------------------------------------------------
// TypeBindings.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/DeclaredType.h"
#include "slang/ast/types/NetType.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/syntax/AllSyntax.h"

void registerTypes(nb::module_& m) {
    nb::enum_<IntegralFlags>(m, "IntegralFlags", nb::is_arithmetic())
        .value("Unsigned", IntegralFlags::Unsigned)
        .value("TwoState", IntegralFlags::TwoState)
        .value("Signed", IntegralFlags::Signed)
        .value("FourState", IntegralFlags::FourState)
        .value("Reg", IntegralFlags::Reg);

    nb::class_<Type, Symbol>(m, "Type")
        .def_prop_ro("canonicalType", &Type::getCanonicalType)
        .def_prop_ro("bitWidth", &Type::getBitWidth)
        .def_prop_ro("bitstreamWidth", &Type::getBitstreamWidth)
        .def_prop_ro("selectableWidth", &Type::getSelectableWidth)
        .def_prop_ro("isSigned", &Type::isSigned)
        .def_prop_ro("isFourState", &Type::isFourState)
        .def_prop_ro("isAggregate", &Type::isAggregate)
        .def_prop_ro("isSingular", &Type::isSingular)
        .def_prop_ro("isIntegral", &Type::isIntegral)
        .def_prop_ro("isScalar", &Type::isScalar)
        .def_prop_ro("isPredefinedInteger", &Type::isPredefinedInteger)
        .def_prop_ro("isSimpleBitVector", &Type::isSimpleBitVector)
        .def_prop_ro("hasFixedRange", &Type::hasFixedRange)
        .def_prop_ro("isBooleanConvertible", &Type::isBooleanConvertible)
        .def_prop_ro("isArray", &Type::isArray)
        .def_prop_ro("isStruct", &Type::isStruct)
        .def_prop_ro("isFixedSize", &Type::isFixedSize)
        .def_prop_ro("isSimpleType", &Type::isSimpleType)
        .def_prop_ro("isByteArray", &Type::isByteArray)
        .def_prop_ro("isNumeric", &Type::isNumeric)
        .def_prop_ro("isPackedArray", &Type::isPackedArray)
        .def_prop_ro("isUnpackedArray", &Type::isUnpackedArray)
        .def_prop_ro("isDynamicallySizedArray", &Type::isDynamicallySizedArray)
        .def_prop_ro("isTaggedUnion", &Type::isTaggedUnion)
        .def_prop_ro("isUnpackedStruct", &Type::isUnpackedStruct)
        .def_prop_ro("isPackedUnion", &Type::isPackedUnion)
        .def_prop_ro("isUnpackedUnion", &Type::isUnpackedUnion)
        .def_prop_ro("isAssociativeArray", &Type::isAssociativeArray)
        .def_prop_ro("isQueue", &Type::isQueue)
        .def_prop_ro("isEnum", &Type::isEnum)
        .def_prop_ro("isClass", &Type::isClass)
        .def_prop_ro("isCovergroup", &Type::isCovergroup)
        .def_prop_ro("isFloating", &Type::isFloating)
        .def_prop_ro("isVoid", &Type::isVoid)
        .def_prop_ro("isNull", &Type::isNull)
        .def_prop_ro("isCHandle", &Type::isCHandle)
        .def_prop_ro("isString", &Type::isString)
        .def_prop_ro("isEvent", &Type::isEvent)
        .def_prop_ro("isUnbounded", &Type::isUnbounded)
        .def_prop_ro("isTypeRefType", &Type::isTypeRefType)
        .def_prop_ro("isUntypedType", &Type::isUntypedType)
        .def_prop_ro("isSequenceType", &Type::isSequenceType)
        .def_prop_ro("isPropertyType", &Type::isPropertyType)
        .def_prop_ro("isVirtualInterface", &Type::isVirtualInterface)
        .def_prop_ro("isHandleType", &Type::isHandleType)
        .def_prop_ro("isObjectHandleType", &Type::isObjectHandleType)
        .def_prop_ro("isAlias", &Type::isAlias)
        .def_prop_ro("isError", &Type::isError)
        .def("isMatching", &Type::isMatching, "rhs"_a)
        .def("isEquivalent", &Type::isEquivalent, "rhs"_a)
        .def("isAssignmentCompatible", &Type::isAssignmentCompatible, "rhs"_a)
        .def("isCastCompatible", &Type::isCastCompatible, "rhs"_a)
        .def("isBitstreamCastable", &Type::isBitstreamCastable, "rhs"_a)
        .def("isBitstreamType", &Type::isBitstreamType, "destination"_a = false)
        .def("isDerivedFrom", &Type::isDerivedFrom, "rhs"_a)
        .def("implements", &Type::implements, "rhs"_a)
        .def("isValidForRand", &Type::isValidForRand, "mode"_a, "languageVersion"_a)
        .def("coerceValue", &Type::coerceValue, "value"_a)
        .def_static("getCommonBase", &Type::getCommonBase, byrefint, "left"_a, "right"_a)
        .def_prop_ro("integralFlags", &Type::getIntegralFlags)
        .def_prop_ro("defaultValue", &Type::getDefaultValue)
        .def_prop_ro("fixedRange", &Type::getFixedRange)
        .def_prop_ro("arrayElementType", &Type::getArrayElementType)
        .def_prop_ro("associativeIndexType", &Type::getAssociativeIndexType)
        .def_prop_ro("canBeStringLike", &Type::canBeStringLike)
        .def_prop_ro("isIterable", &Type::isIterable)
        .def_prop_ro("isValidForDPIReturn", &Type::isValidForDPIReturn)
        .def_prop_ro("isValidForDPIArg", &Type::isValidForDPIArg)
        .def_prop_ro("isValidForSequence", &Type::isValidForSequence)
        .def("__repr__", &Type::toString);

    nb::class_<NetType, Symbol> netType(m, "NetType");
    netType.def_ro("declaredType", &NetType::declaredType)
        .def_ro("netKind", &NetType::netKind)
        .def_prop_ro("resolutionFunction", &NetType::getResolutionFunction)
        .def_prop_ro("isError", &NetType::isError)
        .def_prop_ro("isBuiltIn", &NetType::isBuiltIn)
        .def_static("getSimulatedNetType", &NetType::getSimulatedNetType, byrefint, "internal"_a,
                    "external"_a, "shouldWarn"_a);

    nb::enum_<NetType::NetKind>(netType, "NetKind")
        .value("Unknown", NetType::Unknown)
        .value("Wire", NetType::Wire)
        .value("WAnd", NetType::WAnd)
        .value("WOr", NetType::WOr)
        .value("Tri", NetType::Tri)
        .value("TriAnd", NetType::TriAnd)
        .value("TriOr", NetType::TriOr)
        .value("Tri0", NetType::Tri0)
        .value("Tri1", NetType::Tri1)
        .value("TriReg", NetType::TriReg)
        .value("Supply0", NetType::Supply0)
        .value("Supply1", NetType::Supply1)
        .value("UWire", NetType::UWire)
        .value("Interconnect", NetType::Interconnect)
        .value("UserDefined", NetType::UserDefined)
        .export_values();

    nb::class_<TypePrintingOptions> typePrintingOptions(m, "TypePrintingOptions");
    typePrintingOptions.def_rw("quoteChar", &TypePrintingOptions::quoteChar)
        .def_rw("elideScopeNames", &TypePrintingOptions::elideScopeNames)
        .def_rw("printAKA", &TypePrintingOptions::printAKA)
        .def_rw("skipScopedTypeNames", &TypePrintingOptions::skipScopedTypeNames)
        .def_rw("skipTypeDefs", &TypePrintingOptions::skipTypeDefs)
        .def_rw("fullEnumType", &TypePrintingOptions::fullEnumType)
        .def_rw("typedefsAsLinks", &TypePrintingOptions::typedefsAsLinks)
        .def_rw("enumsAsLinks", &TypePrintingOptions::enumsAsLinks)
        .def_rw("classesAsLinks", &TypePrintingOptions::classesAsLinks)
        .def_rw("printIntegralRange", &TypePrintingOptions::printIntegralRange)
        .def_rw("anonymousTypeStyle", &TypePrintingOptions::anonymousTypeStyle)
        .def_rw("friendlyMemberCharLimit", &TypePrintingOptions::friendlyMemberCharLimit);

    nb::enum_<TypePrintingOptions::AnonymousTypeStyle>(typePrintingOptions, "AnonymousTypeStyle")
        .value("SystemName", TypePrintingOptions::SystemName)
        .value("FriendlyName", TypePrintingOptions::FriendlyName)
        .export_values();

    nb::class_<TypePrinter>(m, "TypePrinter")
        .def(nb::init<>())
        .def_rw("options", &TypePrinter::options)
        .def("append", &TypePrinter::append, "type"_a)
        .def("clear", &TypePrinter::clear)
        .def("toString", &TypePrinter::toString);

    nb::class_<DeclaredType>(m, "DeclaredType")
        .def_prop_ro("type", &DeclaredType::getType)
        .def_prop_ro("typeSyntax", &DeclaredType::getTypeSyntax)
        .def_prop_ro("initializer", &DeclaredType::getInitializer)
        .def_prop_ro("initializerSyntax", &DeclaredType::getInitializerSyntax)
        .def_prop_ro("initializerLocation", &DeclaredType::getInitializerLocation)
        .def_prop_ro("isEvaluating", &DeclaredType::isEvaluating)
        .def_prop_ro("resolvedDimensions", &DeclaredType::getResolvedDimensions);

    nb::class_<IntegralType, Type>(m, "IntegralType")
        .def("getBitVectorRange", &IntegralType::getBitVectorRange)
        .def("isDeclaredReg", &IntegralType::isDeclaredReg);

    nb::class_<ScalarType, IntegralType> scalarType(m, "ScalarType");
    scalarType.def_ro("scalarKind", &ScalarType::scalarKind);

    nb::enum_<ScalarType::Kind>(scalarType, "Kind")
        .value("Bit", ScalarType::Bit)
        .value("Logic", ScalarType::Logic)
        .value("Reg", ScalarType::Reg)
        .export_values();

    nb::class_<PredefinedIntegerType, IntegralType> pdit(m, "PredefinedIntegerType");
    pdit.def_ro("integerKind", &PredefinedIntegerType::integerKind);

    nb::enum_<PredefinedIntegerType::Kind>(pdit, "Kind")
        .value("ShortInt", PredefinedIntegerType::ShortInt)
        .value("Int", PredefinedIntegerType::Int)
        .value("LongInt", PredefinedIntegerType::LongInt)
        .value("Byte", PredefinedIntegerType::Byte)
        .value("Integer", PredefinedIntegerType::Integer)
        .value("Time", PredefinedIntegerType::Time)
        .export_values();

    nb::class_<FloatingType, Type> floating(m, "FloatingType");
    floating.def_ro("floatKind", &FloatingType::floatKind);

    nb::enum_<FloatingType::Kind>(floating, "Kind")
        .value("Real", FloatingType::Real)
        .value("ShortReal", FloatingType::ShortReal)
        .value("RealTime", FloatingType::RealTime)
        .export_values();

    scopeClass<EnumType, IntegralType>(m, "EnumType")
        .def_prop_ro("baseType", [](const EnumType& self) { return &self.baseType; })
        .def_ro("systemId", &EnumType::systemId);

    nb::class_<PackedArrayType, IntegralType>(m, "PackedArrayType")
        .def_prop_ro("elementType", [](const PackedArrayType& self) { return &self.elementType; })
        .def_ro("range", &PackedArrayType::range);

    nb::class_<FixedSizeUnpackedArrayType, Type>(m, "FixedSizeUnpackedArrayType")
        .def_prop_ro("elementType",
                     [](const FixedSizeUnpackedArrayType& self) { return &self.elementType; })
        .def_ro("range", &FixedSizeUnpackedArrayType::range);

    nb::class_<DynamicArrayType, Type>(m, "DynamicArrayType")
        .def_prop_ro("elementType", [](const DynamicArrayType& self) { return &self.elementType; });

    nb::class_<DPIOpenArrayType, Type>(m, "DPIOpenArrayType")
        .def_ro("isPacked", &DPIOpenArrayType::isPacked)
        .def_prop_ro("elementType", [](const DPIOpenArrayType& self) { return &self.elementType; });

    nb::class_<AssociativeArrayType, Type>(m, "AssociativeArrayType")
        .def_prop_ro("elementType",
                     [](const AssociativeArrayType& self) { return &self.elementType; })
        .def_prop_ro("indexType", [](const AssociativeArrayType& self) { return self.indexType; });

    nb::class_<QueueType, Type>(m, "QueueType")
        .def_prop_ro("elementType", [](const QueueType& self) { return &self.elementType; })
        .def_ro("maxBound", &QueueType::maxBound);

    scopeClass<PackedStructType, IntegralType>(m, "PackedStructType")
        .def_ro("systemId", &PackedStructType::systemId);

    scopeClass<UnpackedStructType, Type>(m, "UnpackedStructType")
        .def_ro("systemId", &UnpackedStructType::systemId);

    scopeClass<PackedUnionType, IntegralType>(m, "PackedUnionType")
        .def_ro("systemId", &PackedUnionType::systemId)
        .def_ro("isTagged", &PackedUnionType::isTagged)
        .def_ro("isSoft", &PackedUnionType::isSoft)
        .def_ro("tagBits", &PackedUnionType::tagBits);

    scopeClass<UnpackedUnionType, Type>(m, "UnpackedUnionType")
        .def_ro("systemId", &UnpackedUnionType::systemId)
        .def_ro("isTagged", &UnpackedUnionType::isTagged);

#define SIMPLE_TYPE(name) nb::class_<name, Type>(m, #name)
    SIMPLE_TYPE(VoidType);
    SIMPLE_TYPE(NullType);
    SIMPLE_TYPE(CHandleType);
    SIMPLE_TYPE(StringType);
    SIMPLE_TYPE(EventType);
    SIMPLE_TYPE(UnboundedType);
    SIMPLE_TYPE(TypeRefType);
    SIMPLE_TYPE(UntypedType);
    SIMPLE_TYPE(SequenceType);
    SIMPLE_TYPE(PropertyType);
    SIMPLE_TYPE(ErrorType);

    nb::class_<VirtualInterfaceType, Type>(m, "VirtualInterfaceType")
        .def_prop_ro("iface", [](const VirtualInterfaceType& self) { return &self.iface; })
        .def_prop_ro("modport", [](const VirtualInterfaceType& self) { return self.modport; });

    EXPOSE_ENUM(m, ForwardTypeRestriction);

    nb::class_<ForwardingTypedefSymbol, Symbol>(m, "ForwardingTypedefSymbol")
        .def_ro("typeRestriction", &ForwardingTypedefSymbol::typeRestriction)
        .def_ro("visibility", &ForwardingTypedefSymbol::visibility)
        .def_prop_ro("nextForwardDecl",
                     [](const ForwardingTypedefSymbol& self) { return self.getNextForwardDecl(); });

    nb::class_<TypeAliasType, Type>(m, "TypeAliasType")
        .def_prop_ro("targetType", [](const TypeAliasType& self) { return &self.targetType; })
        .def_ro("visibility", &TypeAliasType::visibility)
        .def_prop_ro("firstForwardDecl",
                     [](const TypeAliasType& self) { return self.getFirstForwardDecl(); });

    scopeClass<ClassType, Type>(m, "ClassType")
        .def_ro("genericClass", &ClassType::genericClass)
        .def_ro("isAbstract", &ClassType::isAbstract)
        .def_ro("isInterface", &ClassType::isInterface)
        .def_ro("isFinal", &ClassType::isFinal)
        .def_ro("thisVar", &ClassType::thisVar)
        .def_prop_ro("baseClass", &ClassType::getBaseClass)
        .def_prop_ro("implementedInterfaces", &ClassType::getImplementedInterfaces)
        .def_prop_ro("baseConstructorCall", &ClassType::getBaseConstructorCall)
        .def_prop_ro("constructor", &ClassType::getConstructor)
        .def_prop_ro("firstForwardDecl", &ClassType::getFirstForwardDecl)
        .def_prop_ro("properties", [](const ClassType& self) {
            nb::list result;
            for (auto& prop : self.properties())
                result.append(nb::cast(&prop));
            return result;
        });

    nb::class_<GenericClassDefSymbol, Symbol>(m, "GenericClassDefSymbol")
        .def_ro("isInterface", &GenericClassDefSymbol::isInterface)
        .def_prop_ro("defaultSpecialization", &GenericClassDefSymbol::getDefaultSpecialization)
        .def_prop_ro("invalidSpecialization", &GenericClassDefSymbol::getInvalidSpecialization)
        .def_prop_ro("defaultSpecialization", &GenericClassDefSymbol::getDefaultSpecialization)
        .def_prop_ro("firstForwardDecl", &GenericClassDefSymbol::getFirstForwardDecl);

    nb::enum_<ConstraintBlockFlags>(m, "ConstraintBlockFlags", nb::is_arithmetic())
        .value("None_", ConstraintBlockFlags::None)
        .value("Pure", ConstraintBlockFlags::Pure)
        .value("Static", ConstraintBlockFlags::Static)
        .value("Extern", ConstraintBlockFlags::Extern)
        .value("ExplicitExtern", ConstraintBlockFlags::ExplicitExtern)
        .value("Initial", ConstraintBlockFlags::Initial)
        .value("Extends", ConstraintBlockFlags::Extends)
        .value("Final", ConstraintBlockFlags::Final);

    scopeClass<ConstraintBlockSymbol, Symbol>(m, "ConstraintBlockSymbol")
        .def_ro("thisVar", &ConstraintBlockSymbol::thisVar)
        .def_ro("flags", &ConstraintBlockSymbol::flags)
        .def_prop_ro("constraints", &ConstraintBlockSymbol::getConstraints);

    scopeClass<CovergroupType, Type>(m, "CovergroupType")
        .def_prop_ro("arguments", &CovergroupType::getArguments)
        .def_prop_ro("body", [](const CovergroupType& self) { return &self.getBody(); })
        .def_prop_ro("baseGroup", &CovergroupType::getBaseGroup)
        .def_prop_ro("coverageEvent", &CovergroupType::getCoverageEvent);
}

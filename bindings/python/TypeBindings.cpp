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

void registerTypes(py::module_& m) {
    py::enum_<IntegralFlags>(m, "IntegralFlags")
        .value("Unsigned", IntegralFlags::Unsigned)
        .value("TwoState", IntegralFlags::TwoState)
        .value("Signed", IntegralFlags::Signed)
        .value("FourState", IntegralFlags::FourState)
        .value("Reg", IntegralFlags::Reg);

    py::class_<Type, Symbol>(m, "Type")
        .def_property_readonly("canonicalType", &Type::getCanonicalType)
        .def_property_readonly("bitWidth", &Type::getBitWidth)
        .def_property_readonly("bitstreamWidth", &Type::getBitstreamWidth)
        .def_property_readonly("selectableWidth", &Type::getSelectableWidth)
        .def_property_readonly("isSigned", &Type::isSigned)
        .def_property_readonly("isFourState", &Type::isFourState)
        .def_property_readonly("isAggregate", &Type::isAggregate)
        .def_property_readonly("isSingular", &Type::isSingular)
        .def_property_readonly("isIntegral", &Type::isIntegral)
        .def_property_readonly("isScalar", &Type::isScalar)
        .def_property_readonly("isPredefinedInteger", &Type::isPredefinedInteger)
        .def_property_readonly("isSimpleBitVector", &Type::isSimpleBitVector)
        .def_property_readonly("hasFixedRange", &Type::hasFixedRange)
        .def_property_readonly("isBooleanConvertible", &Type::isBooleanConvertible)
        .def_property_readonly("isArray", &Type::isArray)
        .def_property_readonly("isStruct", &Type::isStruct)
        .def_property_readonly("isFixedSize", &Type::isFixedSize)
        .def_property_readonly("isSimpleType", &Type::isSimpleType)
        .def_property_readonly("isByteArray", &Type::isByteArray)
        .def_property_readonly("isNumeric", &Type::isNumeric)
        .def_property_readonly("isPackedArray", &Type::isPackedArray)
        .def_property_readonly("isUnpackedArray", &Type::isUnpackedArray)
        .def_property_readonly("isDynamicallySizedArray", &Type::isDynamicallySizedArray)
        .def_property_readonly("isTaggedUnion", &Type::isTaggedUnion)
        .def_property_readonly("isUnpackedStruct", &Type::isUnpackedStruct)
        .def_property_readonly("isPackedUnion", &Type::isPackedUnion)
        .def_property_readonly("isUnpackedUnion", &Type::isUnpackedUnion)
        .def_property_readonly("isAssociativeArray", &Type::isAssociativeArray)
        .def_property_readonly("isQueue", &Type::isQueue)
        .def_property_readonly("isEnum", &Type::isEnum)
        .def_property_readonly("isClass", &Type::isClass)
        .def_property_readonly("isCovergroup", &Type::isCovergroup)
        .def_property_readonly("isFloating", &Type::isFloating)
        .def_property_readonly("isVoid", &Type::isVoid)
        .def_property_readonly("isNull", &Type::isNull)
        .def_property_readonly("isCHandle", &Type::isCHandle)
        .def_property_readonly("isString", &Type::isString)
        .def_property_readonly("isEvent", &Type::isEvent)
        .def_property_readonly("isUnbounded", &Type::isUnbounded)
        .def_property_readonly("isTypeRefType", &Type::isTypeRefType)
        .def_property_readonly("isUntypedType", &Type::isUntypedType)
        .def_property_readonly("isSequenceType", &Type::isSequenceType)
        .def_property_readonly("isPropertyType", &Type::isPropertyType)
        .def_property_readonly("isVirtualInterface", &Type::isVirtualInterface)
        .def_property_readonly("isHandleType", &Type::isHandleType)
        .def_property_readonly("isAlias", &Type::isAlias)
        .def_property_readonly("isError", &Type::isError)
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
        .def("makeSigned", &Type::makeSigned, "compilation"_a)
        .def("makeUnsigned", &Type::makeUnsigned, "compilation"_a)
        .def_static("getCommonBase", &Type::getCommonBase, byrefint, "left"_a, "right"_a)
        .def_property_readonly("integralFlags", &Type::getIntegralFlags)
        .def_property_readonly("defaultValue", &Type::getDefaultValue)
        .def_property_readonly("fixedRange", &Type::getFixedRange)
        .def_property_readonly("arrayElementType", &Type::getArrayElementType)
        .def_property_readonly("associativeIndexType", &Type::getAssociativeIndexType)
        .def_property_readonly("canBeStringLike", &Type::canBeStringLike)
        .def_property_readonly("isIterable", &Type::isIterable)
        .def_property_readonly("isValidForDPIReturn", &Type::isValidForDPIReturn)
        .def_property_readonly("isValidForDPIArg", &Type::isValidForDPIArg)
        .def_property_readonly("isValidForSequence", &Type::isValidForSequence)
        .def("__repr__", &Type::toString);

    py::class_<NetType, Symbol> netType(m, "NetType");
    netType.def_readonly("declaredType", &NetType::declaredType)
        .def_readonly("netKind", &NetType::netKind)
        .def_property_readonly("resolutionFunction", &NetType::getResolutionFunction)
        .def_property_readonly("isError", &NetType::isError)
        .def_property_readonly("isBuiltIn", &NetType::isBuiltIn)
        .def_static("getSimulatedNetType", &NetType::getSimulatedNetType, byrefint, "internal"_a,
                    "external"_a, "shouldWarn"_a);

    py::enum_<NetType::NetKind>(netType, "NetKind")
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

    py::class_<TypePrintingOptions> typePrintingOptions(m, "TypePrintingOptions");
    typePrintingOptions.def_readwrite("addSingleQuotes", &TypePrintingOptions::addSingleQuotes)
        .def_readwrite("elideScopeNames", &TypePrintingOptions::elideScopeNames)
        .def_readwrite("printAKA", &TypePrintingOptions::printAKA)
        .def_readwrite("anonymousTypeStyle", &TypePrintingOptions::anonymousTypeStyle)
        .def_readwrite("skipScopedTypeNames", &TypePrintingOptions::skipScopedTypeNames)
        .def_readwrite("fullEnumType", &TypePrintingOptions::fullEnumType)
        .def_readwrite("skipTypeDefs", &TypePrintingOptions::skipTypeDefs);

    py::enum_<TypePrintingOptions::AnonymousTypeStyle>(typePrintingOptions, "AnonymousTypeStyle")
        .value("SystemName", TypePrintingOptions::SystemName)
        .value("FriendlyName", TypePrintingOptions::FriendlyName)
        .export_values();

    py::class_<TypePrinter>(m, "TypePrinter")
        .def(py::init<>())
        .def_readwrite("options", &TypePrinter::options)
        .def("append", &TypePrinter::append, "type"_a)
        .def("clear", &TypePrinter::clear)
        .def("toString", &TypePrinter::toString);

    py::class_<DeclaredType>(m, "DeclaredType")
        .def_property_readonly("type", &DeclaredType::getType)
        .def_property_readonly("typeSyntax", &DeclaredType::getTypeSyntax)
        .def_property_readonly("initializer", &DeclaredType::getInitializer)
        .def_property_readonly("initializerSyntax", &DeclaredType::getInitializerSyntax)
        .def_property_readonly("initializerLocation", &DeclaredType::getInitializerLocation)
        .def_property_readonly("isEvaluating", &DeclaredType::isEvaluating);

    py::class_<IntegralType, Type>(m, "IntegralType")
        .def("getBitVectorRange", &IntegralType::getBitVectorRange)
        .def("isDeclaredReg", &IntegralType::isDeclaredReg);

    py::class_<ScalarType, IntegralType> scalarType(m, "ScalarType");
    scalarType.def_readonly("scalarKind", &ScalarType::scalarKind);

    py::enum_<ScalarType::Kind>(scalarType, "Kind")
        .value("Bit", ScalarType::Bit)
        .value("Logic", ScalarType::Logic)
        .value("Reg", ScalarType::Reg)
        .export_values();

    py::class_<PredefinedIntegerType, IntegralType> pdit(m, "PredefinedIntegerType");
    pdit.def_readonly("integerKind", &PredefinedIntegerType::integerKind);

    py::enum_<PredefinedIntegerType::Kind>(pdit, "Kind")
        .value("ShortInt", PredefinedIntegerType::ShortInt)
        .value("Int", PredefinedIntegerType::Int)
        .value("LongInt", PredefinedIntegerType::LongInt)
        .value("Byte", PredefinedIntegerType::Byte)
        .value("Integer", PredefinedIntegerType::Integer)
        .value("Time", PredefinedIntegerType::Time)
        .export_values();

    py::class_<FloatingType, Type> floating(m, "FloatingType");
    floating.def_readonly("floatKind", &FloatingType::floatKind);

    py::enum_<FloatingType::Kind>(floating, "Kind")
        .value("Real", FloatingType::Real)
        .value("ShortReal", FloatingType::ShortReal)
        .value("RealTime", FloatingType::RealTime)
        .export_values();

    py::class_<EnumType, IntegralType, Scope>(m, "EnumType")
        .def_property_readonly("baseType", [](const EnumType& self) { return &self.baseType; })
        .def_readonly("systemId", &EnumType::systemId);

    py::class_<PackedArrayType, IntegralType>(m, "PackedArrayType")
        .def_property_readonly("elementType",
                               [](const PackedArrayType& self) { return &self.elementType; })
        .def_readonly("range", &PackedArrayType::range);

    py::class_<FixedSizeUnpackedArrayType, Type>(m, "FixedSizeUnpackedArrayType")
        .def_property_readonly(
            "elementType", [](const FixedSizeUnpackedArrayType& self) { return &self.elementType; })
        .def_readonly("range", &FixedSizeUnpackedArrayType::range);

    py::class_<DynamicArrayType, Type>(m, "DynamicArrayType")
        .def_property_readonly("elementType",
                               [](const DynamicArrayType& self) { return &self.elementType; });

    py::class_<DPIOpenArrayType, Type>(m, "DPIOpenArrayType")
        .def_readonly("isPacked", &DPIOpenArrayType::isPacked)
        .def_property_readonly("elementType",
                               [](const DPIOpenArrayType& self) { return &self.elementType; });

    py::class_<AssociativeArrayType, Type>(m, "AssociativeArrayType")
        .def_property_readonly("elementType",
                               [](const AssociativeArrayType& self) { return &self.elementType; })
        .def_property_readonly("indexType",
                               [](const AssociativeArrayType& self) { return self.indexType; });

    py::class_<QueueType, Type>(m, "QueueType")
        .def_property_readonly("elementType",
                               [](const QueueType& self) { return &self.elementType; })
        .def_readonly("maxBound", &QueueType::maxBound);

    py::class_<PackedStructType, IntegralType, Scope>(m, "PackedStructType")
        .def_readonly("systemId", &PackedStructType::systemId);

    py::class_<UnpackedStructType, Type, Scope>(m, "UnpackedStructType")
        .def_readonly("systemId", &UnpackedStructType::systemId);

    py::class_<PackedUnionType, IntegralType, Scope>(m, "PackedUnionType")
        .def_readonly("systemId", &PackedUnionType::systemId)
        .def_readonly("isTagged", &PackedUnionType::isTagged)
        .def_readonly("isSoft", &PackedUnionType::isSoft)
        .def_readonly("tagBits", &PackedUnionType::tagBits);

    py::class_<UnpackedUnionType, Type, Scope>(m, "UnpackedUnionType")
        .def_readonly("systemId", &UnpackedUnionType::systemId)
        .def_readonly("isTagged", &UnpackedUnionType::isTagged);

#define SIMPLE_TYPE(name) py::class_<name, Type>(m, #name)
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

    py::class_<VirtualInterfaceType, Type>(m, "VirtualInterfaceType")
        .def_property_readonly("iface",
                               [](const VirtualInterfaceType& self) { return &self.iface; })
        .def_property_readonly("modport",
                               [](const VirtualInterfaceType& self) { return self.modport; });

    EXPOSE_ENUM(m, ForwardTypeRestriction);

    py::class_<ForwardingTypedefSymbol, Symbol>(m, "ForwardingTypedefSymbol")
        .def_readonly("typeRestriction", &ForwardingTypedefSymbol::typeRestriction)
        .def_readonly("visibility", &ForwardingTypedefSymbol::visibility)
        .def_property_readonly("nextForwardDecl", [](const ForwardingTypedefSymbol& self) {
            return self.getNextForwardDecl();
        });

    py::class_<TypeAliasType, Type>(m, "TypeAliasType")
        .def_property_readonly("targetType",
                               [](const TypeAliasType& self) { return &self.targetType; })
        .def_readonly("visibility", &TypeAliasType::visibility)
        .def_property_readonly("firstForwardDecl", [](const TypeAliasType& self) {
            return self.getFirstForwardDecl();
        });

    py::class_<ClassType, Type, Scope>(m, "ClassType")
        .def_readonly("genericClass", &ClassType::genericClass)
        .def_readonly("isAbstract", &ClassType::isAbstract)
        .def_readonly("isInterface", &ClassType::isInterface)
        .def_readonly("isFinal", &ClassType::isFinal)
        .def_property_readonly("baseClass", &ClassType::getBaseClass)
        .def_property_readonly("implementedInterfaces", &ClassType::getImplementedInterfaces)
        .def_property_readonly("baseConstructorCall", &ClassType::getBaseConstructorCall)
        .def_property_readonly("constructor", &ClassType::getConstructor)
        .def_property_readonly("firstForwardDecl", &ClassType::getFirstForwardDecl);

    py::class_<GenericClassDefSymbol, Symbol>(m, "GenericClassDefSymbol")
        .def_readonly("isInterface", &GenericClassDefSymbol::isInterface)
        .def_property_readonly("defaultSpecialization",
                               &GenericClassDefSymbol::getDefaultSpecialization)
        .def_property_readonly("invalidSpecialization",
                               &GenericClassDefSymbol::getInvalidSpecialization)
        .def_property_readonly("defaultSpecialization",
                               &GenericClassDefSymbol::getDefaultSpecialization)
        .def_property_readonly("firstForwardDecl", &GenericClassDefSymbol::getFirstForwardDecl);

    py::enum_<ConstraintBlockFlags>(m, "ConstraintBlockFlags")
        .value("None_", ConstraintBlockFlags::None)
        .value("Pure", ConstraintBlockFlags::Pure)
        .value("Static", ConstraintBlockFlags::Static)
        .value("Extern", ConstraintBlockFlags::Extern)
        .value("ExplicitExtern", ConstraintBlockFlags::ExplicitExtern)
        .value("Initial", ConstraintBlockFlags::Initial)
        .value("Extends", ConstraintBlockFlags::Extends)
        .value("Final", ConstraintBlockFlags::Final);

    py::class_<ConstraintBlockSymbol, Symbol, Scope>(m, "ConstraintBlockSymbol")
        .def_readonly("thisVar", &ConstraintBlockSymbol::thisVar)
        .def_readonly("flags", &ConstraintBlockSymbol::flags)
        .def_property_readonly("constraints", &ConstraintBlockSymbol::getConstraints);

    py::class_<CovergroupType, Type, Scope>(m, "CovergroupType")
        .def_property_readonly("arguments", &CovergroupType::getArguments)
        .def_property_readonly("body", [](const CovergroupType& self) { return &self.getBody(); })
        .def_property_readonly("baseGroup", &CovergroupType::getBaseGroup)
        .def_property_readonly("coverageEvent", &CovergroupType::getCoverageEvent);
}

//------------------------------------------------------------------------------
// types.cpp
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"
#include "slang/types/DeclaredType.h"
#include "slang/types/NetType.h"
#include "slang/types/TypePrinter.h"

void registerTypes(py::module_& m) {
    py::class_<Type, Symbol>(m, "Type")
        .def_property_readonly("canonicalType", &Type::getCanonicalType)
        .def_property_readonly("bitWidth", &Type::getBitWidth)
        .def_property_readonly("bitstreamWidth", &Type::bitstreamWidth)
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
        .def_property_readonly("isBitstreamType", &Type::isBitstreamType)
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
        .def_property_readonly("isAlias", &Type::isAlias)
        .def_property_readonly("isError", &Type::isError)
        .def("isMatching", &Type::isMatching)
        .def("isEquivalent", &Type::isEquivalent)
        .def("isAssignmentCompatible", &Type::isAssignmentCompatible)
        .def("isCastCompatible", &Type::isCastCompatible)
        .def("isBitstreamCastable", &Type::isBitstreamCastable)
        .def("isDerivedFrom", &Type::isDerivedFrom)
        .def("implements", &Type::implements)
        .def("isValidForRand", &Type::isValidForRand)
        .def("coerceValue", &Type::coerceValue)
        .def_static("getCommonBase", &Type::getCommonBase)
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
        .def_static("getSimulatedNetType", &NetType::getSimulatedNetType);

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
        .def_readwrite("anonymousTypeStyle", &TypePrintingOptions::anonymousTypeStyle);

    py::enum_<TypePrintingOptions::AnonymousTypeStyle>(typePrintingOptions, "AnonymousTypeStyle")
        .value("SystemName", TypePrintingOptions::SystemName)
        .value("FriendlyName", TypePrintingOptions::FriendlyName)
        .export_values();

    py::class_<TypePrinter>(m, "TypePrinter")
        .def(py::init<>())
        .def_readwrite("options", &TypePrinter::options)
        .def("append", &TypePrinter::append)
        .def("clear", &TypePrinter::clear)
        .def("toString", &TypePrinter::toString);

    py::class_<DeclaredType>(m, "DeclaredType")
        .def_property_readonly("type", &DeclaredType::getType)
        .def_property_readonly("typeSyntax", &DeclaredType::getTypeSyntax)
        .def_property_readonly("initializer", &DeclaredType::getInitializer)
        .def_property_readonly("initializerSyntax", &DeclaredType::getInitializerSyntax)
        .def_property_readonly("initializerLocation", &DeclaredType::getInitializerLocation)
        .def_property_readonly("isEvaluating", &DeclaredType::isEvaluating);
}

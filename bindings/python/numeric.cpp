//------------------------------------------------------------------------------
// numeric.cpp
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "pyslang.h"

#include "slang/numeric/ConstantValue.h"
#include "slang/numeric/SVInt.h"
#include "slang/numeric/Time.h"

template<typename T>
struct always_false : std::false_type {};

static SVInt SVIntFromFloat(double value) {
    if (!isnormal(value))
        return SVInt(32, 0, true);

    double bits = ceil(log2(abs(value))) + 1;
    return SVInt::fromDouble(bitwidth_t(bits), value, true);
}

static SVInt SVIntFromPyInt(const py::int_& value) {
    size_t bits = _PyLong_NumBits(value.ptr());
    if (bits == size_t(-1))
        throw py::error_already_set();

    if (bits == 0)
        return SVInt::Zero;

    bits++; // always make room for a sign bit
    size_t numBytes = ((bits - 1) / 32 + 1) * 4;
    std::vector<byte> mem(numBytes);

    int r = _PyLong_AsByteArray(reinterpret_cast<PyLongObject*>(value.ptr()),
                                reinterpret_cast<unsigned char*>(mem.data()), numBytes, 1, 1);
    if (r == -1)
        throw py::error_already_set();

    return SVInt(bitwidth_t(bits), mem, true);
}

static py::int_ PyIntFromSVInt(const SVInt& value) {
    if (value.hasUnknown())
        return 0;

    uint32_t numWords = value.getNumWords();
    size_t numBytes = numWords * SVInt::WORD_SIZE;
    PyObject* obj;

    if (value.isSigned() && value.isNegative()) {
        // Need to fill the top bits with 1's to guarantee the
        // correct representation in Python land.
        std::vector<unsigned char> mem(numBytes);
        memcpy(mem.data(), value.getRawPtr(), numBytes);

        uint64_t word = value.getRawPtr()[numWords - 1];
        uint32_t wordBits = value.getBitWidth() % SVInt::BITS_PER_WORD;
        if (wordBits > 0)
            word |= ~uint64_t(0ULL) << wordBits;

        memcpy(mem.data() + numBytes - SVInt::WORD_SIZE, &word, SVInt::WORD_SIZE);
        obj = _PyLong_FromByteArray(mem.data(), numBytes, 1, value.isSigned());
    }
    else {
        obj = _PyLong_FromByteArray(reinterpret_cast<const unsigned char*>(value.getRawPtr()),
                                    numBytes, 1, value.isSigned());
    }

    if (!obj)
        throw py::error_already_set();

    return py::reinterpret_steal<py::int_>(obj);
}

void registerNumeric(py::module_& m) {
    EXPOSE_ENUM(m, LiteralBase);
    m.def("literalBaseFromChar", &literalBaseFromChar);
    m.def("clog2", py::overload_cast<const SVInt&>(&clog2));

    py::class_<logic_t>(m, "logic_t")
        .def(py::init<>())
        .def(py::init<uint8_t>())
        .def_readwrite("value", &logic_t::value)
        .def_property_readonly("isUnknown", &logic_t::isUnknown)
        .def_readonly_static("x", &logic_t::x)
        .def_readonly_static("z", &logic_t::z)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__and__", &logic_t::operator&)
        .def("__or__", &logic_t::operator|)
        .def("__xor__", &logic_t::operator^)
        .def("__invert__", &logic_t::operator~)
        .def("__int__", [](const logic_t& self) { return self.value; })
        .def("__bool__", [](const logic_t& self) { return bool(self); })
        .def("__repr__", [](const logic_t& self) { return fmt::format("{}", self.toChar()); });

    py::class_<SVInt>(m, "SVInt")
        .def(py::init<>())
        .def(py::init<logic_t>())
        .def(py::init<bitwidth_t, uint64_t, bool>())
        .def(py::init<bitwidth_t, span<const byte>, bool>())
        .def(py::init([](string_view str) { return SVInt::fromString(str); }))
        .def(py::init(&SVIntFromFloat))
        .def(py::init(&SVIntFromPyInt))
        .def_property_readonly("isSigned", &SVInt::isSigned)
        .def_property_readonly("hasUnknown", &SVInt::hasUnknown)
        .def_property_readonly("bitWidth", &SVInt::getBitWidth)
        .def_static("createFillX", &SVInt::createFillX)
        .def_static("createFillZ", &SVInt::createFillZ)
        .def_static("fromDigits", &SVInt::fromDigits)
        .def_static("fromDouble", &SVInt::fromDouble)
        .def_static("fromFloat", &SVInt::fromFloat)
        .def_static("conditional", &SVInt::conditional)
        .def_static("logicalImpl", &SVInt::logicalImpl)
        .def_static("logicalEquiv", &SVInt::logicalEquiv)
        .def_static("concat", &SVInt::concat)
        .def("isNegative", &SVInt::isNegative)
        .def("isOdd", &SVInt::isOdd)
        .def("isEven", &SVInt::isEven)
        .def("setSigned", &SVInt::setSigned)
        .def("setAllOnes", &SVInt::setAllOnes)
        .def("setAllZeros", &SVInt::setAllZeros)
        .def("setAllX", &SVInt::setAllX)
        .def("setAllZ", &SVInt::setAllZ)
        .def("flattenUnknowns", &SVInt::flattenUnknowns)
        .def("shrinkToFit", &SVInt::shrinkToFit)
        .def("toString",
             py::overload_cast<LiteralBase, bool, bitwidth_t>(&SVInt::toString, py::const_))
        .def("shl", py::overload_cast<const SVInt&>(&SVInt::shl, py::const_))
        .def("ashr", py::overload_cast<const SVInt&>(&SVInt::ashr, py::const_))
        .def("lshr", py::overload_cast<const SVInt&>(&SVInt::lshr, py::const_))
        .def("replicate", &SVInt::replicate)
        .def("reductionOr", &SVInt::reductionOr)
        .def("reductionAnd", &SVInt::reductionAnd)
        .def("reductionXor", &SVInt::reductionXor)
        .def("getActiveBits", &SVInt::getActiveBits)
        .def("getMinRepresentedBits", &SVInt::getMinRepresentedBits)
        .def("countLeadingZeros", &SVInt::countLeadingZeros)
        .def("countLeadingOnes", &SVInt::countLeadingOnes)
        .def("countOnes", &SVInt::countOnes)
        .def("countZeros", &SVInt::countZeros)
        .def("countXs", &SVInt::countXs)
        .def("countZs", &SVInt::countZs)
        .def("slice", &SVInt::slice)
        .def("set", &SVInt::set)
        .def("sext", &SVInt::sext)
        .def("isSignExtendedFrom", &SVInt::isSignExtendedFrom)
        .def("signExtendFrom", &SVInt::signExtendFrom)
        .def("zext", &SVInt::zext)
        .def("extend", &SVInt::extend)
        .def("trunc", &SVInt::trunc)
        .def("resize", &SVInt::resize)
        .def("reverse", &SVInt::reverse)
        .def("xnor", &SVInt::xnor)
        .def(-py::self)
        .def(py::self += py::self)
        .def(py::self -= py::self)
        .def(py::self *= py::self)
        .def(py::self /= py::self)
        .def(py::self %= py::self)
        .def(py::self + py::self)
        .def(py::self - py::self)
        .def(py::self * py::self)
        .def(py::self / py::self)
        .def(py::self % py::self)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def(py::self < py::self)
        .def(py::self <= py::self)
        .def(py::self > py::self)
        .def(py::self >= py::self)
        .def(py::self += int())
        .def(py::self -= int())
        .def(py::self *= int())
        .def(py::self /= int())
        .def(py::self %= int())
        .def(py::self + int())
        .def(py::self - int())
        .def(py::self * int())
        .def(py::self / int())
        .def(py::self % int())
        .def(py::self == int())
        .def(py::self != int())
        .def(py::self < int())
        .def(py::self <= int())
        .def(py::self > int())
        .def(py::self >= int())
        .def(hash(py::self))
        .def("__pow__", &SVInt::pow)
        .def("__iand__", &SVInt::operator&=)
        .def("__ior__", &SVInt::operator|=)
        .def("__ixor__", &SVInt::operator^=)
        .def("__and__", &SVInt::operator&)
        .def("__or__", &SVInt::operator|)
        .def("__xor__", &SVInt::operator^)
        .def("__invert__", &SVInt::operator~)
        .def("__iand__", [](SVInt& a, int b) { return a &= b; })
        .def("__ior__", [](SVInt& a, int b) { return a |= b; })
        .def("__ixor__", [](SVInt& a, int b) { return a ^= b; })
        .def("__and__", [](const SVInt& a, int b) { return a & b; })
        .def("__or__", [](const SVInt& a, int b) { return a | b; })
        .def("__xor__", [](const SVInt& a, int b) { return a ^ b; })
        .def("__rand__", [](const SVInt& a, int b) { return a & b; })
        .def("__ror__", [](const SVInt& a, int b) { return a | b; })
        .def("__rxor__", [](const SVInt& a, int b) { return a ^ b; })
        .def("__radd__", [](const SVInt& a, int b) { return a + b; })
        .def("__rsub__", [](const SVInt& a, int b) { return a - b; })
        .def("__rmul__", [](const SVInt& a, int b) { return a * b; })
        .def("__rdiv__", [](const SVInt& a, int b) { return a / b; })
        .def("__rmod__", [](const SVInt& a, int b) { return a % b; })
        .def("__bool__", [](const SVInt& self) { return (bool)self.reductionOr(); })
        .def("__repr__", [](const SVInt& self) { return self.toString(); })
        .def("__getitem__",
             [](const SVInt& self, size_t i) {
                 if (i >= self.getBitWidth())
                     throw py::index_error();
                 return self[int32_t(i)];
             })
        .def("__int__", [](const SVInt& self) { return PyIntFromSVInt(self); })
        .def("__float__", [](const SVInt& self) { return self.toDouble(); });

    py::implicitly_convertible<py::int_, SVInt>();
    py::implicitly_convertible<double, SVInt>();

    EXPOSE_ENUM(m, TimeUnit);
    m.def("suffixToTimeUnit", &suffixToTimeUnit);
    m.def("timeUnitToSuffix", &timeUnitToSuffix);

    py::enum_<TimeScaleMagnitude>(m, "TimeScaleMagnitude")
        .value("One", TimeScaleMagnitude::One)
        .value("Ten", TimeScaleMagnitude::Ten)
        .value("Hundred", TimeScaleMagnitude::Hundred);

    py::class_<TimeScaleValue>(m, "TimeScaleValue")
        .def(py::init<>())
        .def(py::init<TimeUnit, TimeScaleMagnitude>())
        .def(py::init<string_view>())
        .def_readwrite("unit", &TimeScaleValue::unit)
        .def_readwrite("magnitude", &TimeScaleValue::magnitude)
        .def_static("fromLiteral", &TimeScaleValue::fromLiteral)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__repr__", [](const TimeScaleValue& self) { return self.toString(); });

    py::class_<TimeScale>(m, "TimeScale")
        .def(py::init<>())
        .def(py::init<TimeScaleValue, TimeScaleValue>())
        .def_readwrite("base", &TimeScale::base)
        .def_readwrite("precision", &TimeScale::precision)
        .def("apply", &TimeScale::apply)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__repr__", [](const TimeScale& self) { return self.toString(); });

    py::class_<ConstantValue::NullPlaceholder>(m, "Null")
        .def(py::init<>())
        .def("__repr__", [](const ConstantValue::NullPlaceholder&) { return "null"; });

    py::class_<ConstantValue::UnboundedPlaceholder>(m, "Unbounded")
        .def(py::init<>())
        .def("__repr__", [](const ConstantValue::UnboundedPlaceholder&) { return "$"; });

    py::class_<ConstantValue>(m, "ConstantValue")
        .def(py::init<>())
        .def(py::init<const SVInt&>())
        .def(py::init<const std::string&>())
        .def(py::init([](int i) { return ConstantValue(SVInt(i)); }))
        .def(py::init([](double d) { return ConstantValue(real_t(d)); }))
        .def("isContainer", &ConstantValue::isContainer)
        .def("isTrue", &ConstantValue::isTrue)
        .def("isFalse", &ConstantValue::isFalse)
        .def("hasUnknown", &ConstantValue::hasUnknown)
        .def("bitstreamWidth", &ConstantValue::bitstreamWidth)
        .def("getSlice", &ConstantValue::getSlice)
        .def("empty", &ConstantValue::empty)
        .def("size", &ConstantValue::size)
        .def("convertToInt", py::overload_cast<>(&ConstantValue::convertToInt, py::const_))
        .def("convertToInt",
             py::overload_cast<bitwidth_t, bool, bool>(&ConstantValue::convertToInt, py::const_))
        .def("convertToReal", &ConstantValue::convertToReal)
        .def("convertToShortReal", &ConstantValue::convertToShortReal)
        .def("convertToStr", &ConstantValue::convertToStr)
        .def("convertToByteArray", &ConstantValue::convertToByteArray)
        .def("convertToByteQueue", &ConstantValue::convertToByteQueue)
        .def(hash(py::self))
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__bool__", [](const ConstantValue& self) { return bool(self); })
        .def("__repr__", [](const ConstantValue& self) { return self.toString(); })
        .def_property_readonly("value", [](const ConstantValue& self) {
            return std::visit(
                [](auto&& arg) -> py::object {
                    using T = std::decay_t<decltype(arg)>;
                    if constexpr (std::is_same_v<T, std::monostate>)
                        return py::none();
                    else if constexpr (std::is_same_v<T, SVInt>)
                        return py::cast(arg);
                    else if constexpr (std::is_same_v<T, real_t>)
                        return py::cast(double(arg));
                    else if constexpr (std::is_same_v<T, shortreal_t>)
                        return py::cast(float(arg));
                    else if constexpr (std::is_same_v<T, ConstantValue::NullPlaceholder>)
                        return py::cast(arg);
                    else if constexpr (std::is_same_v<T, ConstantValue::UnboundedPlaceholder>)
                        return py::cast(arg);
                    else if constexpr (std::is_same_v<T, ConstantValue::Elements>)
                        return py::cast(arg);
                    else if constexpr (std::is_same_v<T, std::string>)
                        return py::cast(arg);
                    else if constexpr (std::is_same_v<T, ConstantValue::Map>)
                        return py::cast(*arg);
                    else if constexpr (std::is_same_v<T, ConstantValue::Queue>)
                        return py::cast(*arg);
                    else if constexpr (std::is_same_v<T, ConstantValue::Union>)
                        return py::cast(*arg);
                    else
                        static_assert(always_false<T>::value, "Missing case");
                },
                self.getVariant());
        });

    py::implicitly_convertible<SVInt, ConstantValue>();
    py::implicitly_convertible<std::string, ConstantValue>();
    py::implicitly_convertible<int, ConstantValue>();
    py::implicitly_convertible<double, ConstantValue>();

    py::class_<ConstantRange>(m, "ConstantRange")
        .def(py::init<>())
        .def(py::init([](int left, int right) {
            return ConstantRange{left, right};
        }))
        .def_readwrite("left", &ConstantRange::left)
        .def_readwrite("right", &ConstantRange::right)
        .def_property_readonly("width", &ConstantRange::width)
        .def_property_readonly("lower", &ConstantRange::lower)
        .def_property_readonly("upper", &ConstantRange::upper)
        .def_property_readonly("isLittleEndian", &ConstantRange::isLittleEndian)
        .def("reverse", &ConstantRange::reverse)
        .def("subrange", &ConstantRange::subrange)
        .def("translateIndex", &ConstantRange::translateIndex)
        .def("containsPoint", &ConstantRange::containsPoint)
        .def("overlaps", &ConstantRange::overlaps)
        .def("getIndexedRange", &ConstantRange::getIndexedRange)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__repr__", [](const ConstantRange& self) { return self.toString(); });
}

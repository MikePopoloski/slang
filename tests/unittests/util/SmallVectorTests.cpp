// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/catch_template_test_macros.hpp>
#include <list>

#include "slang/util/SmallVector.h"

namespace {

// A helper class that counts the total number of constructor and
// destructor calls.
class Constructable {
private:
    static int numConstructorCalls;
    static int numMoveConstructorCalls;
    static int numCopyConstructorCalls;
    static int numDestructorCalls;
    static int numAssignmentCalls;
    static int numMoveAssignmentCalls;
    static int numCopyAssignmentCalls;

    bool constructed;
    int value;

public:
    Constructable() : constructed(true), value(0) { ++numConstructorCalls; }

    Constructable(int val) : constructed(true), value(val) { ++numConstructorCalls; }

    Constructable(const Constructable& src) : constructed(true) {
        value = src.value;
        ++numConstructorCalls;
        ++numCopyConstructorCalls;
    }

    Constructable(Constructable&& src) : constructed(true) {
        value = src.value;
        src.value = 0;
        ++numConstructorCalls;
        ++numMoveConstructorCalls;
    }

    ~Constructable() {
        CHECK(constructed);
        ++numDestructorCalls;
        constructed = false;
        value = 0;
    }

    Constructable& operator=(const Constructable& src) {
        CHECK(constructed);
        value = src.value;
        ++numAssignmentCalls;
        ++numCopyAssignmentCalls;
        return *this;
    }

    Constructable& operator=(Constructable&& src) {
        CHECK(constructed);
        value = src.value;
        src.value = 0;
        ++numAssignmentCalls;
        ++numMoveAssignmentCalls;
        return *this;
    }

    int getValue() const { return abs(value); }

    static void reset() {
        numConstructorCalls = 0;
        numMoveConstructorCalls = 0;
        numCopyConstructorCalls = 0;
        numDestructorCalls = 0;
        numAssignmentCalls = 0;
        numMoveAssignmentCalls = 0;
        numCopyAssignmentCalls = 0;
    }

    static int getNumConstructorCalls() { return numConstructorCalls; }
    static int getNumMoveConstructorCalls() { return numMoveConstructorCalls; }
    static int getNumCopyConstructorCalls() { return numCopyConstructorCalls; }
    static int getNumDestructorCalls() { return numDestructorCalls; }
    static int getNumAssignmentCalls() { return numAssignmentCalls; }
    static int getNumMoveAssignmentCalls() { return numMoveAssignmentCalls; }
    static int getNumCopyAssignmentCalls() { return numCopyAssignmentCalls; }

    bool operator==(const Constructable& other) const { return getValue() == other.getValue(); }

    std::strong_ordering operator<=>(const Constructable& other) const {
        return getValue() <=> other.getValue();
    }
};

int Constructable::numConstructorCalls;
int Constructable::numMoveConstructorCalls;
int Constructable::numCopyConstructorCalls;
int Constructable::numDestructorCalls;
int Constructable::numAssignmentCalls;
int Constructable::numMoveAssignmentCalls;
int Constructable::numCopyAssignmentCalls;

template<typename TVector, typename... TArgs>
void assertValuesInOrder(TVector& v, TArgs&&... args) {
    auto a = std::array{std::forward<TArgs>(args)...};
    CHECK(std::ranges::equal(v, a, {}, &Constructable::getValue));
}

template<typename TVector>
void assertEmpty(TVector& v) {
    CHECK(0u == v.size());
    CHECK(v.empty());
    CHECK(v.begin() == v.end());
}

// Generate a sequence of values to initialize the vector.
template<typename TVector>
void makeSequence(TVector& v, int start, int end) {
    for (int i = start; i <= end; ++i)
        v.push_back(Constructable(i));
}

template<typename T, auto N>
constexpr static auto numBuiltinElts(const SmallVector<T, N>&) {
    return N;
}

class SmallVectorTestBase {
public:
    SmallVectorTestBase() { Constructable::reset(); }
};

template<typename TVector>
class SmallVectorTest : public SmallVectorTestBase {
protected:
    TVector theVector;
    TVector otherVector;
};

using SmallVectorTestTypes =
    std::tuple<SmallVector<Constructable, 2>, SmallVector<Constructable, 4>,
               SmallVector<Constructable, 5>, SmallVector<Constructable, 9>>;

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ConstructorIterTest", "[small_vec]",
                               SmallVectorTestTypes) {
    int arr[] = {1, 2, 3};
    auto& v = this->theVector;
    v = SmallVector<Constructable, 4>(std::begin(arr), std::end(arr));
    assertValuesInOrder(v, 1, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ConstructorFromSpanSimpleTest", "[small_vec]",
                               SmallVectorTestTypes) {
    std::array<Constructable, 3> stdArray = {Constructable(1), Constructable(2), Constructable(3)};
    std::span<Constructable> array = stdArray;

    auto& v = this->theVector;
    v = TestType(array);
    assertValuesInOrder(v, 1, 2, 3);
    REQUIRE(numBuiltinElts(TestType{}) == numBuiltinElts(v));
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "EmptyVectorTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    assertEmpty(v);
    CHECK(v.rbegin() == v.rend());
    CHECK(0 == Constructable::getNumConstructorCalls());
    CHECK(0 == Constructable::getNumDestructorCalls());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "MoveConstruct", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);

    TestType tt(std::move(v));
    assertValuesInOrder(tt, 1, 2, 3, 4);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "CopyAssign", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);

    SmallVector<Constructable, 2> tt;
    v = v;
    tt = v;
    assertValuesInOrder(tt, 1, 2, 3, 4);

    tt = v;
    assertValuesInOrder(tt, 1, 2, 3, 4);

    v.clear();
    tt = v;
    CHECK(tt.empty());

    makeSequence(v, 1, 4);
    tt.push_back(1);
    tt = v;
    assertValuesInOrder(tt, 1, 2, 3, 4);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ShrinkToFit", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);

    v.shrink_to_fit();
    CHECK(v.capacity() == std::max(v.size(), numBuiltinElts(v)));
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ShrinkToFit back to small", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 5);
    v.pop_back();
    v.pop_back();
    v.pop_back();

    v.shrink_to_fit();
    CHECK(v.capacity() == numBuiltinElts(v));
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "PushPopTest", "[small_vec]",
                               SmallVectorTestTypes) {
    // Track whether the vector will potentially have to grow.
    auto& v = this->theVector;
    bool RequiresGrowth = v.capacity() < 3;

    // Push an element
    v.push_back(Constructable(1));

    assertValuesInOrder(v, 1);
    CHECK_FALSE(v.begin() == v.end());
    CHECK_FALSE(v.empty());

    v.push_back(Constructable(2));
    assertValuesInOrder(v, 1, 2);

    // Insert at beginning. Reserve space to avoid reference invalidation from v[1].
    v.reserve(v.size() + 1);
    v.insert(v.begin(), v[1]);
    assertValuesInOrder(v, 2, 1, 2);

    v.pop_back();
    assertValuesInOrder(v, 2, 1);

    // Pop remaining elements
    v.resize(v.size() - 2);
    assertEmpty(v);

    // Check number of constructor calls. Should be 2 for each list element,
    // one for the argument to push_back, one for the argument to insert,
    // and one for the list element itself.
    if (!RequiresGrowth) {
        CHECK(6 == Constructable::getNumConstructorCalls());
        CHECK(6 == Constructable::getNumDestructorCalls());
    }
    else {
        // If we had to grow the vector, these only have a lower bound, but should
        // always be equal.
        CHECK(6 <= Constructable::getNumConstructorCalls());
        CHECK(Constructable::getNumConstructorCalls() == Constructable::getNumDestructorCalls());
    }
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ClearTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.reserve(2);
    makeSequence(v, 1, 2);
    v.clear();

    assertEmpty(v);
    CHECK(4 == Constructable::getNumConstructorCalls());
    CHECK(4 == Constructable::getNumDestructorCalls());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ResizeShrinkTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.reserve(3);
    makeSequence(v, 1, 3);
    v.resize(1);

    assertValuesInOrder(v, 1);
    CHECK(6 == Constructable::getNumConstructorCalls());
    CHECK(5 == Constructable::getNumDestructorCalls());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "TruncateTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.reserve(3);
    makeSequence(v, 1, 3);
    v.resize(1);

    assertValuesInOrder(v, 1);
    CHECK(6 == Constructable::getNumConstructorCalls());
    CHECK(5 == Constructable::getNumDestructorCalls());

    v.resize(1);
    assertValuesInOrder(v, 1);
    CHECK(6 == Constructable::getNumConstructorCalls());
    CHECK(5 == Constructable::getNumDestructorCalls());

    v.resize(0);
    assertEmpty(v);
    CHECK(6 == Constructable::getNumConstructorCalls());
    CHECK(6 == Constructable::getNumDestructorCalls());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ResizeGrowTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.resize(2);

    CHECK(2 == Constructable::getNumConstructorCalls());
    CHECK(0 == Constructable::getNumDestructorCalls());
    CHECK(2u == v.size());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ResizeForOverwriteGrowTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.resize_for_overwrite(2);

    CHECK(2 == Constructable::getNumConstructorCalls());
    CHECK(0 == Constructable::getNumDestructorCalls());
    CHECK(2u == v.size());

    v.resize_for_overwrite(20);
    CHECK(22 == Constructable::getNumConstructorCalls());
    CHECK(2 == Constructable::getNumDestructorCalls());
    CHECK(20u == v.size());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ResizeWithElementsTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.resize(2);

    Constructable::reset();

    v.resize(4);

    int ctors = Constructable::getNumConstructorCalls();
    CHECK((ctors == 2 || ctors == 4));

    int moveCtors = Constructable::getNumMoveConstructorCalls();
    CHECK((moveCtors == 0 || moveCtors == 2));

    int dtors = Constructable::getNumDestructorCalls();
    CHECK((dtors == 0 || dtors == 2));
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ResizeFillTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.resize(3, Constructable(77));
    assertValuesInOrder(v, 77, 77, 77);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "OverflowTest", "[small_vec]",
                               SmallVectorTestTypes) {
    // Push more elements than the fixed size.
    auto& v = this->theVector;
    makeSequence(v, 1, 10);

    // Test size and values.
    CHECK(10u == v.size());
    for (int i = 0; i < 10; ++i) {
        CHECK(i + 1 == v[i].getValue());
    }

    // Now resize back to fixed size.
    v.resize(1);
    assertValuesInOrder(v, 1);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "IterationTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 2);

    typename TestType::iterator it = v.begin();
    CHECK(*it == v.front());
    CHECK(*it == v[0]);
    CHECK(1 == it->getValue());
    ++it;
    CHECK(*it == v[1]);
    CHECK(*it == v.back());
    CHECK(2 == it->getValue());
    ++it;
    CHECK(it == v.end());
    --it;
    CHECK(*it == v[1]);
    CHECK(2 == it->getValue());
    --it;
    CHECK(*it == v[0]);
    CHECK(1 == it->getValue());

    typename TestType::reverse_iterator rit = v.rbegin();
    CHECK(*rit == v[1]);
    CHECK(2 == rit->getValue());
    ++rit;
    CHECK(*rit == v[0]);
    CHECK(1 == rit->getValue());
    ++rit;
    CHECK(rit == v.rend());
    --rit;
    CHECK(*rit == v[0]);
    CHECK(1 == rit->getValue());
    --rit;
    CHECK(*rit == v[1]);
    CHECK(2 == rit->getValue());

    const TestType constV = v;
    auto crit = constV.rbegin();
    CHECK(crit != constV.rend());
    CHECK(*crit == 2);
    CHECK(constV.front() == 1);
    CHECK(constV.back() == 2);
    CHECK(*constV.data() == 1);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "SwapTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;
    makeSequence(v, 1, 2);
    std::swap(v, u);
    std::swap(v, v);

    assertEmpty(v);
    assertValuesInOrder(u, 1, 2);

    makeSequence(v, 3, 8);
    makeSequence(u, 9, 18);
    std::swap(v, u);

    assertValuesInOrder(u, 3, 4, 5, 6, 7, 8);
    assertValuesInOrder(v, 1, 2, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AppendTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;
    makeSequence(u, 2, 3);

    v.push_back(Constructable(1));
    v.append(u.begin(), u.end());

    assertValuesInOrder(v, 1, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AppendRepeatedTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.append(2, Constructable(77));
    assertValuesInOrder(v, 1, 77, 77);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AppendNonIterTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.append(2, 7);
    assertValuesInOrder(v, 1, 7, 7);
}

struct output_iterator {
    typedef std::output_iterator_tag iterator_category;
    typedef int value_type;
    typedef int difference_type;
    typedef value_type* pointer;
    typedef value_type& reference;
    operator int() { return 2; }
    operator Constructable() { return 7; }
};

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AppendRepeatedNonForwardIterator", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.append(output_iterator(), output_iterator());
    assertValuesInOrder(v, 1, 7, 7);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AppendSmallVector", "[small_vec]",
                               SmallVectorTestTypes) {
    SmallVector<Constructable, 3> otherVector;
    otherVector.assign_range(std::array{7, 7});

    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.append_range(otherVector);
    assertValuesInOrder(v, 1, 7, 7);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AssignTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.assign(2, Constructable(77));
    assertValuesInOrder(v, 77, 77);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AssignRangeTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));

    int arr[] = {1, 2, 3};
    v.assign(std::begin(arr), std::end(arr));
    assertValuesInOrder(v, 1, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AssignNonIterTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.assign(2, 7);
    assertValuesInOrder(v, 7, 7);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "AssignSmallVector", "[small_vec]",
                               SmallVectorTestTypes) {
    SmallVector<Constructable, 3> otherVector;
    otherVector.assign_range(std::array{7, 7});

    auto& v = this->theVector;
    v.push_back(Constructable(1));
    v.assign_range(otherVector);
    assertValuesInOrder(v, 7, 7);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "MoveAssignTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;

    // Set up our vector with a single element, but enough capacity for 4.
    v.reserve(4);
    v.push_back(Constructable(1));

    // Set up the other vector with 2 elements.
    u.push_back(Constructable(2));
    u.push_back(Constructable(3));

    // Move-assign from the other vector.
    v = std::move(u);
    v = std::move(v);

    // Make sure we have the right result.
    assertValuesInOrder(v, 2, 3);

    // Make sure the # of constructor/destructor calls line up. There
    // are two live objects after clearing the other vector.
    u.clear();
    CHECK(Constructable::getNumConstructorCalls() - 2 == Constructable::getNumDestructorCalls());

    // There shouldn't be any live objects any more.
    v.clear();
    CHECK(Constructable::getNumConstructorCalls() == Constructable::getNumDestructorCalls());

    makeSequence(v, 1, 12);
    makeSequence(u, 5, 10);
    v = std::move(u);
    assertValuesInOrder(v, 5, 6, 7, 8, 9, 10);
    v = std::move(u);
    CHECK(v.empty());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "EraseTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 3);

    const auto& theConstVector = v;
    v.erase(theConstVector.begin());
    assertValuesInOrder(v, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "EraseRangeTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 3);

    const auto& theConstVector = v;
    v.erase(theConstVector.begin(), theConstVector.begin() + 2);
    assertValuesInOrder(v, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertTest", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 3);

    typename TestType::iterator it = v.insert(v.begin() + 1, Constructable(77));
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 77, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertCopy", "[small_vec]", SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 3);
    Constructable c(77);

    typename TestType::iterator it = v.insert(v.begin() + 1, c);
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 77, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRepeatedTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);
    Constructable::reset();
    auto it = v.insert(v.begin() + 1, 2, Constructable(16));

    CHECK((Constructable::getNumMoveConstructorCalls() == 2 ||
           Constructable::getNumMoveConstructorCalls() == 6));

    // Move assign the next two to shift them up and make a gap.
    CHECK(1 == Constructable::getNumMoveAssignmentCalls());

    // Copy construct the two new elements from the parameter.
    CHECK(2 == Constructable::getNumCopyAssignmentCalls());

    // One copy for the temporary during insertion.
    CHECK(1 == Constructable::getNumCopyConstructorCalls());
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 16, 16, 2, 3, 4);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRepeatedNonIterTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);
    Constructable::reset();
    auto it = v.insert(v.begin() + 1, 2, 7);
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 7, 7, 2, 3, 4);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRepeatedInMiddlePastEndTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);
    Constructable::reset();
    auto it = v.insert(v.begin() + 1, 5, 7);
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 7, 7, 7, 7, 7, 2, 3, 4);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRepeatedAtEndTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 4);
    Constructable::reset();
    auto it = v.insert(v.end(), 2, Constructable(16));

    // Just copy construct them into newly allocated space
    CHECK(2 + 1 == Constructable::getNumCopyConstructorCalls());

    // Move everything across if reallocation is needed.
    CHECK((Constructable::getNumMoveConstructorCalls() == 0 ||
           Constructable::getNumMoveConstructorCalls() == 4));

    // Without ever moving or copying anything else.
    CHECK(0 == Constructable::getNumCopyAssignmentCalls());
    CHECK(0 == Constructable::getNumMoveAssignmentCalls());

    CHECK(v.begin() + 4 == it);
    assertValuesInOrder(v, 1, 2, 3, 4, 16, 16);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRepeatedEmptyTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 10, 15);

    // Empty insert.
    CHECK(v.end() == v.insert(v.end(), 0, Constructable(42)));
    CHECK(v.begin() + 1 == v.insert(v.begin() + 1, 0, Constructable(42)));
}

// Insert range.
TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRangeTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    Constructable arr[3] = {Constructable(77), Constructable(77), Constructable(77)};

    makeSequence(v, 1, 3);
    Constructable::reset();
    auto it = v.insert_range(v.begin() + 1, arr);

    // Move construct the top 3 elements into newly allocated space.
    // Possibly move the whole sequence into new space first.
    CHECK((Constructable::getNumMoveConstructorCalls() == 2 ||
           Constructable::getNumMoveConstructorCalls() == 5));

    // Copy assign the lower 2 new elements into existing space.
    CHECK(2 == Constructable::getNumCopyAssignmentCalls());

    // Copy construct the third element into newly allocated space.
    CHECK(1 == Constructable::getNumCopyConstructorCalls());
    CHECK(v.begin() + 1 == it);
    assertValuesInOrder(v, 1, 77, 77, 77, 2, 3);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertRangeAtEndTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    Constructable arr[3] = {Constructable(77), Constructable(77), Constructable(77)};

    makeSequence(v, 1, 3);

    // Insert at end.
    Constructable::reset();
    auto it = v.insert(v.end(), arr, arr + 3);

    // Copy construct the 3 elements into new space at the top.
    CHECK(3 == Constructable::getNumCopyConstructorCalls());

    // Don't copy/move anything else.
    CHECK(0 == Constructable::getNumCopyAssignmentCalls());

    // Reallocation might occur, causing all elements to be moved into the new
    // buffer.
    CHECK((Constructable::getNumMoveConstructorCalls() == 0 ||
           Constructable::getNumMoveConstructorCalls() == 3));
    CHECK(0 == Constructable::getNumMoveAssignmentCalls());
    CHECK(v.begin() + 3 == it);
    assertValuesInOrder(v, 1, 2, 3, 77, 77, 77);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "InsertEmptyRangeTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    makeSequence(v, 1, 3);

    // Empty insert.
    CHECK(v.end() == v.insert(v.end(), v.begin(), v.begin()));
    CHECK(v.begin() + 1 == v.insert(v.begin() + 1, v.begin(), v.begin()));
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ComparisonEqualityTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;
    makeSequence(v, 1, 3);
    makeSequence(u, 1, 3);

    CHECK(v == u);
    CHECK_FALSE(v != u);

    u.clear();
    makeSequence(u, 2, 4);

    CHECK_FALSE(v == u);
    CHECK(v != u);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ComparisonLessThanTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;
    v.assign_range(std::array{1, 2, 4});
    u.assign_range(std::array{1, 4});

    CHECK(v < u);
    CHECK(v <= u);
    CHECK_FALSE(v > u);
    CHECK_FALSE(v >= u);

    CHECK_FALSE(u < v);
    CHECK_FALSE(u <= v);
    CHECK(u > v);
    CHECK(u >= v);

    u.assign_range(std::array{1, 2, 4});

    CHECK_FALSE(v < u);
    CHECK(v <= u);
    CHECK_FALSE(v > u);
    CHECK(v >= u);

    CHECK_FALSE(u < v);
    CHECK(u <= v);
    CHECK_FALSE(u > v);
    CHECK(u >= v);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "ConstVectorTest", "[small_vec]",
                               SmallVectorTestTypes) {
    const TestType constVector;

    CHECK(0u == constVector.size());
    CHECK(constVector.empty());
    CHECK(constVector.begin() == constVector.end());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "DirectVectorTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    CHECK(0u == v.size());

    v.reserve(4);
    CHECK(4u <= v.capacity());
    CHECK(0 == Constructable::getNumConstructorCalls());

    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    v.push_back(4);
    CHECK(4u == v.size());
    CHECK(8 == Constructable::getNumConstructorCalls());
    CHECK(1 == v[0].getValue());
    CHECK(2 == v[1].getValue());
    CHECK(3 == v[2].getValue());
    CHECK(4 == v[3].getValue());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorTest, "IteratorTest", "[small_vec]",
                               SmallVectorTestTypes) {
    auto& v = this->theVector;
    std::list<int> l;
    v.insert(v.end(), l.begin(), l.end());
}

template<typename InvalidType>
class DualSmallVectorsTest;

template<typename VectorT1, typename VectorT2>
class DualSmallVectorsTest<std::pair<VectorT1, VectorT2>> : public SmallVectorTestBase {
protected:
    VectorT1 theVector;
    VectorT2 otherVector;
};

using DualSmallVectorTestTypes = std::tuple<
    // Small mode -> Small mode.
    std::pair<SmallVector<Constructable, 4>, SmallVector<Constructable, 4>>,
    // Small mode -> Big mode.
    std::pair<SmallVector<Constructable, 4>, SmallVector<Constructable, 2>>,
    // Big mode -> Small mode.
    std::pair<SmallVector<Constructable, 2>, SmallVector<Constructable, 4>>,
    // Big mode -> Big mode.
    std::pair<SmallVector<Constructable, 2>, SmallVector<Constructable, 2>>>;

TEMPLATE_LIST_TEST_CASE_METHOD(DualSmallVectorsTest, "MoveAssignment", "[small_vec]",
                               DualSmallVectorTestTypes) {
    auto& v = this->theVector;
    auto& u = this->otherVector;

    // Set up our vector with four elements.
    for (unsigned it = 0; it < 4; ++it)
        u.push_back(Constructable(it));

    const Constructable* origDataPtr = u.data();

    // Move-assign from the other vector.
    v = std::move(u);

    // Make sure we have the right result.
    assertValuesInOrder(v, 0, 1, 2, 3);

    // Make sure the # of constructor/destructor calls line up. There
    // are two live objects after clearing the other vector.
    u.clear();
    CHECK(Constructable::getNumConstructorCalls() - 4 == Constructable::getNumDestructorCalls());

    // If the source vector (otherVector) was in small-mode, assert that we just
    // moved the data pointer over.
    CHECK((numBuiltinElts(u) == 4 || v.data() == origDataPtr));

    // There shouldn't be any live objects any more.
    v.clear();
    CHECK(Constructable::getNumConstructorCalls() == Constructable::getNumDestructorCalls());

    // We shouldn't have copied anything in this whole process.
    CHECK(Constructable::getNumCopyConstructorCalls() == 0);
}

enum class EmplaceableArgState { Defaulted, Arg, LValue, RValue, Failure };
template<int it>
struct EmplaceableArg {
    EmplaceableArgState state;

    EmplaceableArg() : state(EmplaceableArgState::Defaulted) {}
    EmplaceableArg(EmplaceableArg&& x) :
        state(x.state == EmplaceableArgState::Arg ? EmplaceableArgState::RValue
                                                  : EmplaceableArgState::Failure) {}
    EmplaceableArg(EmplaceableArg& x) :
        state(x.state == EmplaceableArgState::Arg ? EmplaceableArgState::LValue
                                                  : EmplaceableArgState::Failure) {}

    explicit EmplaceableArg(bool) : state(EmplaceableArgState::Arg) {}

private:
    EmplaceableArg& operator=(EmplaceableArg&&) = delete;
    EmplaceableArg& operator=(const EmplaceableArg&) = delete;
};

enum class EmplaceableState { Emplaced, Moved };
struct Emplaceable {
    EmplaceableArg<0> a0;
    EmplaceableArg<1> a1;
    EmplaceableArg<2> a2;
    EmplaceableArg<3> a3;
    EmplaceableState state;

    Emplaceable() : state(EmplaceableState::Emplaced) {}

    template<typename A0Ty>
    explicit Emplaceable(A0Ty&& a0) :
        a0(std::forward<A0Ty>(a0)), state(EmplaceableState::Emplaced) {}

    template<typename A0Ty, class A1Ty>
    Emplaceable(A0Ty&& a0, A1Ty&& a1) :
        a0(std::forward<A0Ty>(a0)), a1(std::forward<A1Ty>(a1)), state(EmplaceableState::Emplaced) {}

    template<typename A0Ty, class A1Ty, class A2Ty>
    Emplaceable(A0Ty&& a0, A1Ty&& a1, A2Ty&& a2) :
        a0(std::forward<A0Ty>(a0)), a1(std::forward<A1Ty>(a1)), a2(std::forward<A2Ty>(a2)),
        state(EmplaceableState::Emplaced) {}

    template<typename A0Ty, class A1Ty, class A2Ty, class A3Ty>
    Emplaceable(A0Ty&& a0, A1Ty&& a1, A2Ty&& a2, A3Ty&& a3) :
        a0(std::forward<A0Ty>(a0)), a1(std::forward<A1Ty>(a1)), a2(std::forward<A2Ty>(a2)),
        a3(std::forward<A3Ty>(a3)), state(EmplaceableState::Emplaced) {}

    Emplaceable(Emplaceable&&) : state(EmplaceableState::Moved) {}
    Emplaceable& operator=(Emplaceable&&) {
        state = EmplaceableState::Moved;
        return *this;
    }

private:
    Emplaceable(const Emplaceable&) = delete;
    Emplaceable& operator=(const Emplaceable&) = delete;
};

TEST_CASE("SmallVector::EmplaceBack", "[small_vec]") {
    EmplaceableArg<0> a0(true);
    EmplaceableArg<1> a1(true);
    EmplaceableArg<2> a2(true);
    EmplaceableArg<3> a3(true);
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back();
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::Defaulted);
        CHECK(back.a1.state == EmplaceableArgState::Defaulted);
        CHECK(back.a2.state == EmplaceableArgState::Defaulted);
        CHECK(back.a3.state == EmplaceableArgState::Defaulted);
    }
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back(std::move(a0));
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::RValue);
        CHECK(back.a1.state == EmplaceableArgState::Defaulted);
        CHECK(back.a2.state == EmplaceableArgState::Defaulted);
        CHECK(back.a3.state == EmplaceableArgState::Defaulted);
    }
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back(a0);
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::LValue);
        CHECK(back.a1.state == EmplaceableArgState::Defaulted);
        CHECK(back.a2.state == EmplaceableArgState::Defaulted);
        CHECK(back.a3.state == EmplaceableArgState::Defaulted);
    }
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back(a0, a1);
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::LValue);
        CHECK(back.a1.state == EmplaceableArgState::LValue);
        CHECK(back.a2.state == EmplaceableArgState::Defaulted);
        CHECK(back.a3.state == EmplaceableArgState::Defaulted);
    }
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back(std::move(a0), std::move(a1));
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::RValue);
        CHECK(back.a1.state == EmplaceableArgState::RValue);
        CHECK(back.a2.state == EmplaceableArgState::Defaulted);
        CHECK(back.a3.state == EmplaceableArgState::Defaulted);
    }
    {
        SmallVector<Emplaceable, 3> v;
        Emplaceable& back = v.emplace_back(std::move(a0), a1, std::move(a2), a3);
        CHECK(&back == &v.back());
        CHECK(v.size() == 1);
        CHECK(back.state == EmplaceableState::Emplaced);
        CHECK(back.a0.state == EmplaceableArgState::RValue);
        CHECK(back.a1.state == EmplaceableArgState::LValue);
        CHECK(back.a2.state == EmplaceableArgState::RValue);
        CHECK(back.a3.state == EmplaceableArgState::LValue);
    }
    {
        SmallVector<int, 2> v;
        v.emplace_back();
        v.emplace_back(42);
        CHECK(2U == v.size());
        CHECK(0 == v[0]);
        CHECK(42 == v[1]);
    }
}

TEST_CASE("SmallVector::DefaultInlinedElements", "[small_vec]") {
    SmallVector<int> v;
    CHECK(v.empty());
    v.push_back(7);
    CHECK(v[0] == 7);

    // Check that at least a couple layers of nested SmallVector<T>'s are allowed
    // by the default inline elements policy.
    SmallVector<SmallVector<SmallVector<int>>> nestedV;
    nestedV.emplace_back().emplace_back().emplace_back(42);
    CHECK(nestedV[0][0][0] == 42);
}

struct To {
    int content;
    bool operator==(const To& other) const = default;
};

class From {
public:
    From() = default;
    From(To m) { t = m; }
    operator To() const { return t; }

private:
    To t;
};

TEST_CASE("SmallVector::ConstructFromArrayRefOfConvertibleType", "[small_vec]") {
    To to1{1}, to2{2}, to3{3};
    std::vector<From> stdVector = {From(to1), From(to2), From(to3)};
    std::span<From> array = stdVector;
    {
        SmallVector<To> vector(array);

        REQUIRE(array.size() == vector.size());
        for (size_t it = 0; it < array.size(); ++it)
            CHECK(array[it] == vector[it]);
    }
    {
        SmallVector<To, 4> vector(stdVector);

        REQUIRE(stdVector.size() == vector.size());
        REQUIRE(4u == numBuiltinElts(vector));
        for (size_t it = 0; it < stdVector.size(); ++it)
            CHECK(stdVector[it] == vector[it]);
    }
}

template<typename TVector>
class SmallVectorReferenceInvalidationTest : public SmallVectorTestBase {
protected:
    TVector v;

    template<typename T>
    static bool isValueType() {
        return std::is_same_v<T, typename TVector::value_type>;
    }

    SmallVectorReferenceInvalidationTest() {
        // Fill up the small size so that insertions move the elements.
        for (int it = 0, e = numBuiltinElts(v); it != e; ++it)
            v.emplace_back(it + 1);
    }
};

// Test one type that's trivially copyable (int) and one that isn't (Constructable)
// since reference invalidation may be fixed differently for each.
using SmallVectorReferenceInvalidationTestTypes =
    std::tuple<SmallVector<int, 3>, SmallVector<Constructable, 3>>;

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "PushBack", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;
    int n = numBuiltinElts(v);

    // Push back a reference to last element when growing from small storage.
    v.push_back(v.back());
    CHECK(n == v.back());

    // Check that the old value is still there (not moved away).
    CHECK(n == v[v.size() - 2]);

    // Fill storage again.
    v.back() = v.size();
    while (v.size() < v.capacity())
        v.push_back(v.size() + 1);

    // Push back a reference to last element when growing from large storage.
    v.push_back(v.back());
    CHECK(int(v.size()) - 1 == v.back());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "PushBackMoved", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;
    int n = numBuiltinElts(v);

    // Push back a reference to last element when growing from small storage.
    v.push_back(std::move(v.back()));
    CHECK(n == v.back());
    if (this->template isValueType<Constructable>()) {
        // Check that the value was moved (not copied).
        CHECK(0 == v[v.size() - 2]);
    }

    // Fill storage again.
    v.back() = v.size();
    while (v.size() < v.capacity())
        v.push_back(v.size() + 1);

    // Push back a reference to last element when growing from large storage.
    v.push_back(std::move(v.back()));

    // Check the values.
    CHECK(int(v.size()) - 1 == v.back());
    if (this->template isValueType<Constructable>()) {
        // Check the value got moved out.
        CHECK(0 == v[v.size() - 2]);
    }
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "Resize", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    auto& v = this->v;
    int n = numBuiltinElts(v);
    v.resize(n + 1, v.back());
    CHECK(n == v.back());

    // Resize to add enough elements that v will grow again.
    v.resize(v.capacity() + 1, v.front());
    CHECK(1 == v.back());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "Append", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    auto& v = this->v;
    v.append(1, v.back());
    int n = numBuiltinElts(v);
    CHECK(n == v[n - 1]);

    // Append enough more elements that v will grow again. This tests growing
    // when already in large mode.
    v.append(v.capacity() - v.size() + 1, v.front());
    CHECK(1 == v.back());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "Assign", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;
    int n = numBuiltinElts(v);
    REQUIRE(unsigned(n) == v.size());
    REQUIRE(unsigned(n) == v.capacity());

    // Check assign that shrinks in small mode.
    v.assign(1, v.back());
    CHECK(1u == v.size());
    CHECK(n == v[0]);

    // Check assign that grows within small mode.
    REQUIRE(v.size() <= v.capacity());
    v.assign(v.capacity(), v.back());
    for (int it = 0, e = v.size(); it != e; ++it) {
        CHECK(n == v[it]);

        // Reset to [1, 2, ...].
        v[it] = it + 1;
    }

    // Check assign that grows to large mode.
    REQUIRE(2 == v[1]);
    v.assign(v.capacity() + 1, v[1]);
    for (int it = 0, e = v.size(); it != e; ++it) {
        CHECK(2 == v[it]);

        // Reset to [1, 2, ...].
        v[it] = it + 1;
    }

    // Check assign that shrinks in large mode.
    v.assign(1, v[1]);
    CHECK(2 == v[0]);
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "AssignRange", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    auto& v = this->v;
    v.assign(v.begin(), v.begin());
    CHECK(v.empty());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "Insert", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;

    // Insert a reference to the back (not at end() or else insert delegates to
    // push_back()), growing out of small mode. Confirm the value was copied out
    // (moving out Constructable sets it to 0).
    v.insert(v.begin(), v.back());
    CHECK(int(v.size() - 1) == v.front());
    CHECK(int(v.size() - 1) == v.back());

    // Fill up the vector again.
    while (v.size() < v.capacity())
        v.push_back(v.size() + 1);

    // Grow again from large storage to large storage.
    v.insert(v.begin(), v.back());
    CHECK(int(v.size() - 1) == v.front());
    CHECK(int(v.size() - 1) == v.back());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "InsertMoved", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;

    // Insert a reference to the back (not at end() or else insert delegates to
    // push_back()), growing out of small mode. Confirm the value was copied out
    // (moving out Constructable sets it to 0).
    v.insert(v.begin(), std::move(v.back()));
    CHECK(int(v.size() - 1) == v.front());
    if (this->template isValueType<Constructable>()) {
        // Check the value got moved out.
        CHECK(0 == v.back());
    }

    // Fill up the vector again.
    while (v.size() < v.capacity())
        v.push_back(v.size() + 1);

    // Grow again from large storage to large storage.
    v.insert(v.begin(), std::move(v.back()));
    CHECK(int(v.size() - 1) == v.front());
    if (this->template isValueType<Constructable>()) {
        // Check the value got moved out.
        CHECK(0 == v.back());
    }
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "InsertN", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Cover NumToInsert <= this->end() - it.
    auto& v = this->v;
    v.insert(v.begin() + 1, 1, v.back());
    int n = numBuiltinElts(v);
    CHECK(n == v[1]);

    // Cover NumToInsert > this->end() - it, inserting enough elements that v will
    // also grow again; v.capacity() will be more elements than necessary but
    // it's a simple way to cover both conditions.
    v.insert(v.begin(), v.capacity(), v.front());
    CHECK(1 == v.front());
}

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorReferenceInvalidationTest, "EmplaceBack", "[small_vec]",
                               SmallVectorReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;
    int n = numBuiltinElts(v);

    // Push back a reference to last element when growing from small storage.
    v.emplace_back(v.back());
    CHECK(n == v.back());

    // Check that the old value is still there (not moved away).
    CHECK(n == v[v.size() - 2]);

    // Fill storage again.
    v.back() = v.size();
    while (v.size() < v.capacity())
        v.push_back(v.size() + 1);

    // Push back a reference to last element when growing from large storage.
    v.emplace_back(v.back());
    CHECK(int(v.size()) - 1 == v.back());
}

template<typename TVector>
class SmallVectorInternalReferenceInvalidationTest : public SmallVectorTestBase {
protected:
    TVector v;

    SmallVectorInternalReferenceInvalidationTest() {
        // Fill up the small size so that insertions move the elements.
        for (int it = 0, e = numBuiltinElts(v); it != e; ++it)
            v.emplace_back(it + 1, it + 1);
    }
};

using SmallVectorInternalReferenceInvalidationTestTypes =
    std::tuple<SmallVector<std::pair<int, int>, 3>,
               SmallVector<std::pair<Constructable, Constructable>, 3>>;

TEMPLATE_LIST_TEST_CASE_METHOD(SmallVectorInternalReferenceInvalidationTest, "EmplaceBack",
                               "[small_vec]", SmallVectorInternalReferenceInvalidationTestTypes) {
    // Note: setup adds [1, 2, ...] to v until it's at capacity in small mode.
    auto& v = this->v;
    int n = numBuiltinElts(v);

    // Push back a reference to last element when growing from small storage.
    v.emplace_back(v.back().first, v.back().second);
    CHECK(n == v.back().first);
    CHECK(n == v.back().second);

    // Check that the old value is still there (not moved away).
    CHECK(n == v[v.size() - 2].first);
    CHECK(n == v[v.size() - 2].second);

    // Fill storage again.
    v.back().first = v.back().second = v.size();
    while (v.size() < v.capacity())
        v.emplace_back((int)v.size() + 1, (int)v.size() + 1);

    // Push back a reference to last element when growing from large storage.
    v.emplace_back(v.back().first, v.back().second);
    CHECK(int(v.size()) - 1 == v.back().first);
    CHECK(int(v.size()) - 1 == v.back().second);
}

struct NotAssignable {
    int& x;
    NotAssignable(int& x) : x(x) {}
};

TEST_CASE("SmallVector::NoAssignTest", "[small_vec]") {
    int x = 0;
    SmallVector<NotAssignable, 2> vec;
    vec.push_back(NotAssignable(x));

    x = 42;
    CHECK(42 == vec.back().x);
}

struct MovedFrom {
    bool hasValue;
    MovedFrom() : hasValue(true) {}
    MovedFrom(MovedFrom&& m) : hasValue(m.hasValue) { m.hasValue = false; }
    MovedFrom& operator=(MovedFrom&& m) {
        hasValue = m.hasValue;
        m.hasValue = false;
        return *this;
    }
};

TEST_CASE("SmallVector::MidInsert", "[small_vec]") {
    SmallVector<MovedFrom, 3> v;
    v.push_back(MovedFrom());
    v.insert(v.begin(), MovedFrom());
    for (MovedFrom& m : v)
        CHECK(m.hasValue);
}

#if __cpp_exceptions
TEST_CASE("SmallVector::resize error", "[small_vec]") {
    SmallVector<int, 2> vec;
    CHECK_THROWS(vec.resize(SIZE_MAX));
}
#endif

#if __cpp_exceptions
TEST_CASE("SmallVector::reserve error", "[small_vec]") {
    SmallVector<int, 2> vec;
    CHECK_THROWS(vec.reserve(SIZE_MAX));
}
#endif

TEST_CASE("SmallVector::resize more than double", "[small_vec]") {
    SmallVector<int, 2> vec;
    vec.resize(32);
    CHECK(vec.size() == 32);
    CHECK(vec.capacity() == 32);
}

TEST_CASE("SmallVector::Emplace at back", "[small_vec]") {
    Constructable::reset();
    SmallVector<Constructable, 2> vec;
    vec.emplace(vec.end(), 1);
    vec.emplace(vec.end(), 2);

    CHECK(Constructable::getNumConstructorCalls() == 2);
}

TEST_CASE("SmallVector::copy/ccopy", "[small_vec]") {
    SmallVector<Constructable, 2> vec;
    makeSequence(vec, 1, 4);

    BumpAllocator alloc;
    std::span<Constructable> s1 = vec.copy(alloc);
    CHECK(std::ranges::equal(s1, vec));

    std::span<const Constructable> s2 = vec.ccopy(alloc);
    CHECK(std::ranges::equal(s2, vec));

    vec.clear();
    s1 = vec.copy(alloc);
    CHECK(s1.empty());
}

#if __cpp_exceptions
TEST_CASE("SmallVector::at", "[small_vec]") {
    SmallVector<Constructable, 2> vec;
    makeSequence(vec, 1, 4);

    CHECK(vec.at(2) == 3);
    CHECK_THROWS(vec.at(4));

    const SmallVector<Constructable, 2> cv = vec;
    CHECK(cv.at(2) == 3);
    CHECK(cv.at(3) == cv[3]);
    CHECK_THROWS(cv.at(4));
}
#endif

TEST_CASE("SmallVector::uninitialized construct", "[small_vec]") {
    SmallVector<Constructable, 2> vec(32, UninitializedTag{});
    CHECK(vec.empty());
    CHECK(vec.capacity() == 32);
}

} // end namespace

//------------------------------------------------------------------------------
// EvalContext.h
// Expression evaluation context.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <map>
#include <stack>
#include <vector>

#include "binding/ConstantValue.h"
#include "symbols/Symbol.h"

namespace slang {

class EvalContext;
class FieldSymbol;
class ValueSymbol;

/// An lvalue is anything that can appear on the left hand side of an assignment
/// expression. It represents some storage location in memory that can be read
/// from and written to.
///
struct LValue {
    /// A concatenation of lvalues is also an lvalue and can be assigned to.
    struct Concat { std::vector<LValue> elements; };

    /// The root of an lvalue path is some kind of variable or a further
    /// concatenation of other lvalues.
    using Root = std::variant<const ValueSymbol*, Concat>;

    /// One step in an lvalue path: selecting an element from an array.
    struct ElementSelect { int32_t index; };

    /// One step in an lvalue path: selecting a range of elements from an array.
    /// Note that this is only valid at the end of a path.
    struct RangeSelect { int32_t left; int32_t right; };

    /// One step in an lvalue path: selecting a member of a complex object.
    struct MemberSelect { const FieldSymbol* field; };

    /// The lvalue path is made up of various select elements.
    using PathElement = std::variant<ElementSelect, RangeSelect, MemberSelect>;

    Root root;
    std::vector<PathElement> path;

    LValue() = default;
    LValue(nullptr_t) {}
    explicit LValue(const ValueSymbol& value) : root(&value) {}
    explicit LValue(Concat&& concat) : root(std::move(concat)) {}

    ConstantValue load(EvalContext& context) const;
    void store(EvalContext& context, const ConstantValue& value);

    void selectElement(int32_t index);
    void selectRange(int32_t left, int32_t right);
    void selectMember(const FieldSymbol& field);

    explicit operator bool() const { return root.index() > 0 || std::get<0>(root); }
};

/// A container for all context required to evaluate an expression.
/// Mostly this involves tracking the callstack and maintaining
/// storage for local variables.
class EvalContext {
public:
    EvalContext();

    /// Creates storage for a local variable in the current frame.
    ConstantValue* createLocal(const Symbol* symbol, ConstantValue value);

    /// Gets the current value for the given local variable symbol.
    /// Returns nullptr if the symbol cannot be found.
    ConstantValue* findLocal(const Symbol* symbol);

    /// Push a new frame onto the call stack.
    void pushFrame();

    /// Pop the active frame from the call stack and returns its value, if any.
    ConstantValue popFrame();

    // TODO: get rid of this
    bool hasReturned() { return stack.top().hasReturned; }
    void setReturned(ConstantValue value) { stack.top().hasReturned = true; stack.top().returnValue = std::move(value); }

private:
    // Represents a single frame in the call stack.
    struct Frame {
        // A set of temporary values materialized within the stack frame.
        // Use a map so that the values don't move around in memory.
        std::map<const Symbol*, ConstantValue> temporaries;

        // Set to non-null when a return has been issued in this frame.
        ConstantValue returnValue;
        bool hasReturned = false;
    };

    std::stack<Frame> stack;
};

}
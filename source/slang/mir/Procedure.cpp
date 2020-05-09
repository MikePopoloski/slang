//------------------------------------------------------------------------------
// Procedure.cpp
// MIR procedures (always, initial, etc)
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/mir/Procedure.h"

#include "slang/binding/Statements.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/mir/MIRBuilder.h"
#include "slang/mir/MIRPrinter.h"
#include "slang/symbols/ASTVisitor.h"

namespace {

using namespace slang;
using namespace slang::mir;

class ProcedureVisitor {
public:
    Procedure& proc;

    ProcedureVisitor(Procedure& proc) : proc(proc) {}

    void visit(const EmptyStatement&) {}
    void visit(const StatementList& list) {
        for (auto stmt : list.list)
            stmt->visit(*this);
    }

    void visit(const BlockStatement& block) { block.getStatements().visit(*this); }
    void visit(const ExpressionStatement& stmt) { stmt.expr.visit(*this); }

    void visit(const VariableDeclStatement&) {}
    void visit(const ReturnStatement&) {}
    void visit(const BreakStatement&) {}
    void visit(const ContinueStatement&) {}
    void visit(const ConditionalStatement&) {}
    void visit(const CaseStatement&) {}
    void visit(const ForLoopStatement&) {}
    void visit(const RepeatLoopStatement&) {}
    void visit(const ForeachLoopStatement&) {}
    void visit(const WhileLoopStatement&) {}
    void visit(const DoWhileLoopStatement&) {}
    void visit(const ForeverLoopStatement&) {}
    void visit(const TimedStatement&) {}
    void visit(const AssertionStatement&) {}

    MIRValue visit(const IntegerLiteral&) { return {}; }
    MIRValue visit(const RealLiteral&) { return {}; }
    MIRValue visit(const TimeLiteral&) { return {}; }
    MIRValue visit(const UnbasedUnsizedIntegerLiteral&) { return {}; }
    MIRValue visit(const NullLiteral&) { return {}; }
    MIRValue visit(const StringLiteral&) { return {}; }
    MIRValue visit(const NamedValueExpression&) { return {}; }
    MIRValue visit(const UnaryExpression&) { return {}; }
    MIRValue visit(const BinaryExpression&) { return {}; }
    MIRValue visit(const ConditionalExpression&) { return {}; }
    MIRValue visit(const InsideExpression&) { return {}; }
    MIRValue visit(const AssignmentExpression&) { return {}; }
    MIRValue visit(const ConcatenationExpression&) { return {}; }
    MIRValue visit(const ReplicationExpression&) { return {}; }
    MIRValue visit(const ElementSelectExpression&) { return {}; }
    MIRValue visit(const RangeSelectExpression&) { return {}; }
    MIRValue visit(const MemberAccessExpression&) { return {}; }

    MIRValue visit(const CallExpression& call) {
        if (call.isSystemCall()) {
            std::get<1>(call.subroutine).subroutine->lower(proc, call.arguments());
            return {};
        }
        return {};
    }

    MIRValue visit(const ConversionExpression&) { return {}; }
    MIRValue visit(const DataTypeExpression&) { return {}; }
    MIRValue visit(const SimpleAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const StructuredAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const ReplicatedAssignmentPatternExpression&) { return {}; }
    MIRValue visit(const EmptyArgumentExpression&) { return {}; }
    MIRValue visit(const OpenRangeExpression&) { return {}; }

    void visitInvalid(const Statement&) {}
    MIRValue visitInvalid(const Expression&) { return {}; }
};

} // namespace

namespace slang::mir {

Procedure::Procedure(MIRBuilder& builder, const ProceduralBlockSymbol& procedure) :
    builder(builder) {
    ProcedureVisitor visitor(*this);
    procedure.getBody().visit(visitor);
}

MIRValue Procedure::emitExpr(const Expression& expr) {
    ProcedureVisitor visitor(*this);
    return expr.visit(visitor);
}

MIRValue Procedure::emitConst(const Type& type, const ConstantValue& val) {
    return MIRValue(*constantAlloc.emplace(type, val));
}

MIRValue Procedure::emitConst(const Type& type, ConstantValue&& val) {
    return MIRValue(*constantAlloc.emplace(type, std::move(val)));
}

MIRValue Procedure::emitCall(SysCallKind sysCall, const Type& returnType,
                             span<const MIRValue> args) {
    instructions.emplace_back(sysCall, returnType, copyValues(args));
    return MIRValue(instructions.size() - 1);
}

void Procedure::emitCall(SysCallKind sysCall, span<const MIRValue> args) {
    emitCall(sysCall, builder.compilation.getVoidType(), args);
}

void Procedure::emitCall(SysCallKind sysCall, MIRValue arg0) {
    emitCall(sysCall, { &arg0, 1 });
}

Compilation& Procedure::getCompilation() const {
    return builder.compilation;
}

std::string Procedure::toString() const {
    return MIRPrinter().print(*this).str();
}

span<const MIRValue> Procedure::copyValues(span<const MIRValue> values) {
    if (values.empty())
        return {};

    size_t bytes = sizeof(MIRValue) * values.size();
    auto data = (MIRValue*)alloc.allocate(bytes, alignof(MIRValue));
    memcpy(data, values.data(), bytes);

    return { data, values.size() };
}

} // namespace slang::mir
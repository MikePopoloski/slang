//------------------------------------------------------------------------------
// CodeGenerator.cpp
// Executable code generation
// NOTE: Only included if slang is configured to use LLVM
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/codegen/CodeGenerator.h"

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4702) // unreachable code
#endif
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/TargetSelect.h>
#ifdef _MSC_VER
#    pragma warning(pop)
#endif

#include "slang/codegen/ExpressionEmitter.h"
#include "slang/codegen/StatementEmitter.h"
#include "slang/compilation/Compilation.h"
#include "slang/mir/Procedure.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/Symbol.h"

namespace slang {

using namespace mir;

GeneratedCode::GeneratedCode(std::unique_ptr<llvm::LLVMContext> context,
                             std::unique_ptr<llvm::Module> module) :
    context(std::move(context)),
    module(std::move(module)) {
}

GeneratedCode::GeneratedCode(GeneratedCode&&) = default;
GeneratedCode::~GeneratedCode() = default;

std::pair<std::unique_ptr<llvm::LLVMContext>, std::unique_ptr<llvm::Module>> GeneratedCode::
    release() {
    return { std::move(context), std::move(module) };
}

std::string GeneratedCode::toString() const {
    std::string result;
    llvm::raw_string_ostream os(result);
    module->print(os, nullptr);
    return os.str();
}

CodeGenerator::CodeGenerator(Compilation& compilation) : compilation(compilation) {
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();
    llvm::InitializeNativeTargetAsmParser();

    ctx = std::make_unique<llvm::LLVMContext>();
    module = std::make_unique<llvm::Module>("primary", *ctx);

    // Register built-in types.
    typeMap.emplace(&compilation.getVoidType(), llvm::Type::getVoidTy(*ctx));

    // Create the main entry point.
    auto intType = llvm::Type::getInt32Ty(*ctx);
    auto funcType = llvm::FunctionType::get(intType, /* isVarArg */ false);
    mainFunc = llvm::Function::Create(funcType, llvm::Function::ExternalLinkage, "main", *module);

    // Create the first basic block that will run at the start of simulation
    // to initialize all static variables.
    globalInitBlock = llvm::BasicBlock::Create(*ctx, "", mainFunc);
}

CodeGenerator::~CodeGenerator() = default;

void CodeGenerator::generate(const Procedure& proc) {
    auto funcType = llvm::FunctionType::get(llvm::Type::getVoidTy(*ctx), /* isVarArg */ false);
    auto func = llvm::Function::Create(funcType, llvm::Function::PrivateLinkage, "", *module);
    auto bb = llvm::BasicBlock::Create(*ctx, "", func);

    IRBuilder ir(bb);
    for (auto& instr : proc.getInstructions())
        emit(ir, instr);

    ir.CreateRetVoid();

    IRBuilder caller(globalInitBlock);
    caller.CreateCall(func, {});
}

llvm::Value* CodeGenerator::emit(IRBuilder& ir, const Instr& instr) {
    switch (instr.kind) {
        case InstrKind::SysCall:
            return emitSysCall(ir, instr);
        case InstrKind::Invalid:
            return ir.CreateUnreachable();
    }
    THROW_UNREACHABLE;
}

llvm::Value* CodeGenerator::emit(IRBuilder&, const MIRValue& val) {
    switch (val.getKind()) {
        case MIRValue::Constant: {
            auto& tcv = val.asConstant();
            return genConstant(tcv.type, tcv.value);
        }
        case MIRValue::InstrSlot:
        case MIRValue::Global:
        case MIRValue::Local:
        case MIRValue::Empty:
            // TODO:
            break;
    }
    THROW_UNREACHABLE;
}

llvm::Value* CodeGenerator::emitSysCall(IRBuilder& ir, const Instr& instr) {
    SmallVectorSized<llvm::Value*, 8> args;
    for (auto& op : instr.getOperands())
        args.append(emit(ir, op));

    return ir.CreateCall(getSysFunc(instr.getSysCallKind()),
                         llvm::makeArrayRef(args.data(), args.size()));
}

llvm::Function* CodeGenerator::getSysFunc(SysCallKind kind) {
    if (auto it = sysFunctions.find(kind); it != sysFunctions.end())
        return it->second;

    auto void_t = llvm::Type::getVoidTy(*ctx);
    auto int8_t = llvm::Type::getInt8Ty(*ctx);

    llvm::Function* func = nullptr;
    switch (kind) {
        case SysCallKind::PrintChar:
            func = llvm::Function::Create(
                llvm::FunctionType::get(void_t, { int8_t }, /* isVarArg */ false),
                llvm::Function::ExternalLinkage, "printChar", *module);
            break;
    }

    ASSERT(func);
    sysFunctions.emplace(kind, func);
    return func;
}

GeneratedCode CodeGenerator::finish() {
    // Insert all initial blocks into the main function.
    auto lastBlock = globalInitBlock;
    for (auto block : initialBlocks) {
        llvm::IRBuilder<>(lastBlock).CreateBr(block);
        lastBlock = block;
    }

    // Finish the main function.
    auto intType = llvm::Type::getInt32Ty(*ctx);
    llvm::IRBuilder<>(lastBlock).CreateRet(llvm::ConstantInt::get(intType, 0));

    // Verify all generated code.
    bool bad = llvm::verifyModule(*module, &llvm::errs());
    if (bad)
        module->dump();

    return GeneratedCode(std::move(ctx), std::move(module));
}

void CodeGenerator::genInstance(const InstanceSymbol& instance) {
    instance.visit(makeVisitor([this](const VariableSymbol& symbol) { genGlobal(symbol); },
                               [this](const ProceduralBlockSymbol& symbol) { genBlock(symbol); }));
}

void CodeGenerator::genBlock(const ProceduralBlockSymbol& block) {
    // For now skip everything except initial blocks.
    if (block.procedureKind != ProceduralBlockKind::Initial)
        return;

    // Create a block that will contain all of the process's statements.
    auto bb = llvm::BasicBlock::Create(*ctx, "", mainFunc);
    genStmt(bb, block.getBody());
    initialBlocks.push_back(bb);
}

llvm::Type* CodeGenerator::genType(const Type& type) {
    // Unwrap aliases.
    if (type.isAlias())
        return genType(type.getCanonicalType());

    // Check the cache.
    if (auto it = typeMap.find(&type); it != typeMap.end())
        return it->second;

    if (!type.isIntegral())
        THROW_UNREACHABLE;

    // Underlying representation for integer types:
    // - Two state types: use the bitwidth as specified
    // - Four state types: double the specified bitwidth,
    //                     the upper bits indicate a 1 for unknowns
    // - If the actual width > configured limit, switch to an array of bytes
    auto& intType = type.as<IntegralType>();
    uint32_t bits = intType.bitWidth;
    if (intType.isFourState)
        bits *= 2;

    llvm::Type* result;
    if (bits > options.maxIntBits)
        result = llvm::ArrayType::get(llvm::Type::getInt64Ty(*ctx), (bits + 63) / 64);
    else
        result = llvm::Type::getIntNTy(*ctx, bits);

    typeMap.emplace(&type, result);
    return result;
}

llvm::Constant* CodeGenerator::genConstant(const Type& type, const ConstantValue& cv) {
    // TODO: other value types
    return genConstant(type, cv.integer());
}

llvm::Constant* CodeGenerator::genConstant(const Type& type, const SVInt& integer) {
    auto& intType = type.as<IntegralType>();
    uint32_t bits = intType.bitWidth;
    if (intType.isFourState)
        bits *= 2;

    llvm::ArrayRef<uint64_t> data(integer.getRawPtr(), integer.getNumWords());
    if (bits <= options.maxIntBits)
        return llvm::ConstantInt::get(*ctx, llvm::APInt(bits, data));
    else
        return llvm::ConstantDataArray::get(*ctx, data);
}

llvm::Value* CodeGenerator::genExpr(llvm::BasicBlock* bb, const Expression& expr) {
    ExpressionEmitter emitter(*this, bb);
    return emitter.emit(expr);
}

void CodeGenerator::genStmt(llvm::BasicBlock* bb, const Statement& stmt) {
    StatementEmitter emitter(*this, bb);
    emitter.emit(stmt);
}

void CodeGenerator::genGlobal(const VariableSymbol& variable) {
    ASSERT(variable.lifetime == VariableLifetime::Static);

    auto& type = variable.getType();

    bool needsInitializer = false;
    llvm::Constant* constVal = nullptr;
    if (auto init = variable.getInitializer()) {
        EvalContext evCtx(compilation);
        ConstantValue val = init->eval(evCtx);
        if (val)
            constVal = genConstant(type, val);
        else
            needsInitializer = true;
    }

    // If no initializer provided, use the default for the type.
    if (!constVal)
        constVal = genConstant(type, type.getDefaultValue());

    auto global = new llvm::GlobalVariable(*module, genType(type), /* isConstant */ false,
                                           llvm::GlobalValue::PrivateLinkage, constVal);
    globalMap.emplace(&variable, global);

    // If we set needsInitializer, the variable has an initializer expression
    // but it's not constant. Emit it into the basic block that will run at
    // the start of simulation.
    if (needsInitializer) {
        auto expr = genExpr(globalInitBlock, *variable.getInitializer());
        llvm::IRBuilder<> ir(globalInitBlock);
        ir.CreateStore(expr, global);
    }
}

llvm::Function* CodeGenerator::genSubroutine(const SubroutineSymbol&) {
    THROW_UNREACHABLE;
}

llvm::Function* CodeGenerator::genSubroutine(const SystemSubroutine& subroutine) {
    auto it = sysSubroutineMap.find(&subroutine);
    ASSERT(it != sysSubroutineMap.end());
    return it->second;
}

} // namespace slang
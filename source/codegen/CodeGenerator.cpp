//------------------------------------------------------------------------------
// CodeGenerator.cpp
// Top-level code generation API
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/codegen/CodeGenerator.h"

#include "CodegenImpl.h"
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/Verifier.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/TargetParser/Host.h>

#include "slang/ast/Compilation.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"

namespace slang::codegen {

CodeGenerator::CodeGenerator(Compilation& compilation, CodegenOptions options) :
    impl(std::make_unique<Impl>(compilation, std::move(options))) {
}

CodeGenerator::~CodeGenerator() = default;
CodeGenerator::CodeGenerator(CodeGenerator&&) noexcept = default;
CodeGenerator& CodeGenerator::operator=(CodeGenerator&&) noexcept = default;

void CodeGenerator::emitSubroutine(const SubroutineSymbol& subroutine) {
    impl->emitSubroutine(subroutine);
}

void CodeGenerator::emitScope(const Scope& scope) {
    impl->emitScope(scope);
}

void CodeGenerator::emitExports() {
    impl->emitExports();
}

std::string CodeGenerator::getTextualIR() const {
    return impl->getTextualIR();
}

std::string CodeGenerator::writeIRToFile(std::string_view path) const {
    return impl->writeIRToFile(path);
}

std::string CodeGenerator::writeBitcodeToFile(std::string_view path) const {
    return impl->writeBitcodeToFile(path);
}

CodeGenerator::Impl::Impl(Compilation& compilation, CodegenOptions options) :
    // TODO: module name?
    context(compilation, "slang", std::move(options)) {
}

void CodeGenerator::Impl::emitSubroutine(const SubroutineSymbol& subroutine) {
    FunctionEmitter emitter(context);
    emitter.lower(subroutine);
}

void CodeGenerator::Impl::emitScope(const Scope& scope) {
    FunctionEmitter emitter(context);
    for (auto& member : scope.members()) {
        if (member.kind == SymbolKind::Subroutine)
            emitter.lower(member.as<SubroutineSymbol>());
    }
}

void CodeGenerator::Impl::emitExports() {
    // Emit DPI export thunks for all exports.
    FunctionEmitter emitter(context);
    for (auto& [sub, cIdent] : context.compilation.getDPIExports())
        emitter.lowerDPIExport(*sub, cIdent);
}

std::string CodeGenerator::Impl::getTextualIR() const {
    std::string out;
    llvm::raw_string_ostream os(out);
    context.module->print(os, nullptr);
    return out;
}

std::string CodeGenerator::Impl::writeIRToFile(std::string_view path) const {
    if (path == "-") {
        context.module->print(llvm::outs(), nullptr);
        return {};
    }

    std::error_code ec;
    llvm::raw_fd_ostream out(llvm::StringRef(path.data(), path.size()), ec, llvm::sys::fs::OF_Text);
    if (ec)
        return ec.message();
    context.module->print(out, nullptr);
    return {};
}

std::string CodeGenerator::Impl::writeBitcodeToFile(std::string_view path) const {
    if (path == "-") {
        llvm::raw_fd_ostream out(1, /* shouldClose */ false, /* unbuffered */ true);
        llvm::WriteBitcodeToFile(*context.module, out);
        return {};
    }

    std::error_code ec;
    llvm::raw_fd_ostream out(llvm::StringRef(path.data(), path.size()), ec, llvm::sys::fs::OF_None);
    if (ec)
        return ec.message();
    llvm::WriteBitcodeToFile(*context.module, out);
    return {};
}

CodegenContext::CodegenContext(Compilation& compilation, std::string_view moduleName,
                               CodegenOptions opts) :
    ctx(std::make_unique<llvm::LLVMContext>()),
    module(std::make_unique<llvm::Module>(moduleName, *ctx)), compilation(compilation),
    options(std::move(opts)), types(*this) {

    // Initialize the native target (calls are idempotent).
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();

    // Determine the target triple.
    llvm::Triple triple;
    if (options.targetTriple.empty())
        triple = llvm::Triple(llvm::sys::getProcessTriple());
    else
        triple = llvm::Triple(llvm::Triple::normalize(options.targetTriple));

    // Determine CPU name.
    std::string cpuName;
    if (!options.cpu.empty()) {
        cpuName = options.cpu;
    }
    else if (options.targetTriple.empty() ||
             triple.getArch() == llvm::Triple(llvm::sys::getProcessTriple()).getArch()) {
        cpuName = std::string(llvm::sys::getHostCPUName());
    }
    else {
        cpuName = "generic";
    }

    // TODO: report the error here somehow
    std::string error;
    auto target = llvm::TargetRegistry::lookupTarget(triple, error);
    if (target) {
        // TODO: set options?
        // TODO: reloc, code model, opt level, etc
        llvm::TargetOptions targetOpts;
        targetMachine.reset(target->createTargetMachine(triple, cpuName, options.features,
                                                        targetOpts, std::nullopt));
        if (targetMachine) {
            module->setTargetTriple(triple);
            module->setDataLayout(targetMachine->createDataLayout());
        }
    }
}

IRBuilder::IRBuilder(CodegenContext& context) :
    llvm::IRBuilder<>(*context.ctx), types(context.types) {
}

// Convert an SVInt value (or its unknown half) to an LLVM APInt.
static llvm::APInt toAPInt(const SVInt& sv, bool unknownPart) {
    const bitwidth_t bits = sv.getBitWidth();
    const uint32_t numWords = (bits + 63) / 64;
    const auto data = sv.getRawPtr();
    const auto words = unknownPart ? data + numWords : data;
    if (numWords == 1)
        return llvm::APInt(bits, words[0]);

    return llvm::APInt(bits, llvm::ArrayRef<uint64_t>(words, numWords));
}

llvm::ConstantInt* IRBuilder::getSVInt(const SVInt& val, bool isFourState) {
    if (isFourState) {
        const bitwidth_t bits = val.getBitWidth();
        auto valAP = toAPInt(val, false);
        auto unkAP = val.hasUnknown() ? toAPInt(val, true) : llvm::APInt(bits, 0);
        llvm::APInt combined = unkAP.zext(bits * 2).shl(bits) | valAP.zext(bits * 2);
        return llvm::ConstantInt::get(getContext(), combined);
    }
    else {
        SLANG_ASSERT(!val.hasUnknown());
        return llvm::ConstantInt::get(getContext(), toAPInt(val, false));
    }
}

llvm::Value* IRBuilder::createSVInt(llvm::Value* val, llvm::Value* unk, llvm::Type* type) {
    unsigned n = llvm::cast<llvm::IntegerType>(val->getType())->getBitWidth();
    auto vExt = CreateZExt(val, type);
    auto uShl = CreateShl(CreateZExt(unk, type), n);
    return CreateOr(vExt, uShl, "", /* IsDisjoint */ true);
}

llvm::Value* IRBuilder::toFourState(llvm::Value* v) {
    unsigned n = llvm::cast<llvm::IntegerType>(v->getType())->getBitWidth();
    return toFourState(v, getIntNTy(n * 2));
}

llvm::Value* IRBuilder::toFourState(llvm::Value* v, llvm::Type* fourStateTy) {
    // Zero-extend to i(2N); upper N bits (unk) are implicitly zero.
    return CreateZExt(v, fourStateTy);
}

TypeEmitter::TypeEmitter(CodegenContext& context) : context(context) {
    auto& vmCtx = *context.ctx;
    VoidTy = llvm::Type::getVoidTy(vmCtx);
    Int8Ty = llvm::Type::getInt8Ty(vmCtx);
    Int16Ty = llvm::Type::getInt16Ty(vmCtx);
    Int32Ty = llvm::Type::getInt32Ty(vmCtx);
    Int64Ty = llvm::Type::getInt64Ty(vmCtx);
    FloatTy = llvm::Type::getFloatTy(vmCtx);
    DoubleTy = llvm::Type::getDoubleTy(vmCtx);
    PtrTy = llvm::PointerType::get(vmCtx, 0);

    SVLogicVecValTy = llvm::StructType::get(vmCtx, {Int32Ty, Int32Ty});

    auto& comp = context.compilation;
    typeCache[&comp.getVoidType()] = VoidTy;
    typeCache[&comp.getRealType()] = DoubleTy;
    typeCache[&comp.getShortRealType()] = FloatTy;
}

llvm::Type* TypeEmitter::lowerForDPIArg(llvm::LLVMContext& vmCtx, const Type& type) {
    auto& ct = type.getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::VoidType:
            return llvm::Type::getVoidTy(vmCtx);
        case SymbolKind::FloatingType:
            return ct.getBitWidth() == 32 ? llvm::Type::getFloatTy(vmCtx)
                                          : llvm::Type::getDoubleTy(vmCtx);
        case SymbolKind::ScalarType:
            return llvm::IntegerType::get(vmCtx, 8);
        case SymbolKind::PredefinedIntegerType:
            switch (ct.as<PredefinedIntegerType>().integerKind) {
                case PredefinedIntegerType::ShortInt:
                    return llvm::IntegerType::get(vmCtx, 16);
                case PredefinedIntegerType::Int:
                    return llvm::IntegerType::get(vmCtx, 32);
                case PredefinedIntegerType::LongInt:
                    return llvm::IntegerType::get(vmCtx, 64);
                case PredefinedIntegerType::Byte:
                    return llvm::IntegerType::get(vmCtx, 8);
                case PredefinedIntegerType::Integer:
                case PredefinedIntegerType::Time:
                    // 4-state types are passed by pointer to svLogicVecVal array.
                    return llvm::PointerType::get(vmCtx, 0);
            }
            SLANG_UNREACHABLE;
        case SymbolKind::EnumType:
            return lowerForDPIArg(vmCtx, ct.as<EnumType>().baseType);
        case SymbolKind::CHandleType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::PackedStructType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::DPIOpenArrayType:
        case SymbolKind::StringType:
            // Everything else is passed by reference.
            return llvm::PointerType::get(vmCtx, 0);
        default:
            SLANG_UNREACHABLE;
    }
}

llvm::Type* TypeEmitter::lowerForDPIArg(const Type& type) {
    return lowerForDPIArg(*context.ctx, type);
}

llvm::Type* TypeEmitter::lowerForDPILayout(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (auto it = dpiLayoutCache.find(&ct); it != dpiLayoutCache.end())
        return it->second;

    llvm::Type* result = nullptr;
    switch (ct.kind) {
        case SymbolKind::PredefinedIntegerType:
            switch (ct.as<PredefinedIntegerType>().integerKind) {
                case PredefinedIntegerType::Integer:
                    // 32-bit 4-state: 1 x svLogicVecVal
                    result = llvm::ArrayType::get(SVLogicVecValTy, 1);
                    break;
                case PredefinedIntegerType::Time:
                    // 64-bit 4-state: 2 x svLogicVecVal
                    result = llvm::ArrayType::get(SVLogicVecValTy, 2);
                    break;
                default:
                    result = lowerForDPIArg(ct);
                    break;
            }
            break;
        case SymbolKind::PackedArrayType:
        case SymbolKind::PackedStructType: {
            // Packed types use svBitVecVal (uint32_t) or svLogicVecVal chunks.
            const auto bits = ct.getBitWidth();
            const auto numChunks = (bits + 31) / 32;
            if (ct.isFourState())
                result = llvm::ArrayType::get(SVLogicVecValTy, numChunks);
            else
                result = llvm::ArrayType::get(Int32Ty, numChunks);
            break;
        }
        case SymbolKind::FixedSizeUnpackedArrayType: {
            auto& arrTy = ct.as<FixedSizeUnpackedArrayType>();
            auto elemTy = lowerForDPILayout(arrTy.elementType);
            result = llvm::ArrayType::get(elemTy, arrTy.range.width());
            break;
        }
        case SymbolKind::UnpackedStructType: {
            SmallVector<llvm::Type*, 4> fieldTypes;
            for (auto field : ct.as<UnpackedStructType>().fields)
                fieldTypes.push_back(lowerForDPILayout(field->getType()));
            result = llvm::StructType::get(*context.ctx, fieldTypes);
            break;
        }
        default:
            result = lowerForDPIArg(ct);
            break;
    }

    dpiLayoutCache.emplace(&ct, result);
    return result;
}

llvm::Type* TypeEmitter::lower(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (auto it = typeCache.find(&ct); it != typeCache.end())
        return it->second;

    llvm::Type* result = nullptr;
    if (ct.isIntegral()) {
        const bitwidth_t bits = ct.getBitWidth();
        SLANG_ASSERT(bits > 0);

        if (ct.isFourState())
            result = fourStateFor(bits);
        else
            result = twoStateFor(bits);
    }
    else {
        SLANG_UNIMPLEMENTED;
    }

    typeCache.emplace(&ct, result);
    return result;
}

llvm::IntegerType* TypeEmitter::twoStateFor(bitwidth_t bits) {
    return llvm::IntegerType::get(*context.ctx, bits);
}

llvm::IntegerType* TypeEmitter::fourStateFor(bitwidth_t bits) {
    // i(2N): val in [N-1:0], unk in [2N-1:N].
    return llvm::IntegerType::get(*context.ctx, bits * 2);
}

// Computes a mangled LLVM symbol name for an internal SV subroutine.
// TODO: this is not fully sufficient but good enough for now
//
// Format:  _SV0 <path>
// <path>   =  "U"                           (compilation-unit root)
//           | "N" <ns> <path> <identifier>  (nested item)
// <ns>     =  "v" (function/task)
//           | "p" (package)
//           | "m" (module / instance-body / class / other scope)
// <identifier> = <decimal-length> <name>
//
// Examples:
//   function automatic int add(...) in package math
//       -> _SV0NvNpU4math3add
//   top-level function calc
//       -> _SV0NvU4calc
static std::string mangleSubroutineName(const SubroutineSymbol& sub) {
    // Collect path components from the subroutine up to (but not including)
    // the compilation-unit / root boundary.
    SmallVector<const Symbol*, 8> components;
    const Symbol* sym = &sub;
    while (sym) {
        if (!sym->name.empty())
            components.push_back(sym);

        auto parent = sym->getParentScope();
        if (!parent)
            break;

        auto& parentSym = parent->asSymbol();
        if (parentSym.kind == SymbolKind::Root || parentSym.kind == SymbolKind::CompilationUnit)
            break;

        sym = &parentSym;
    }

    // Build the path string from innermost to outermost, wrapping each level
    // in an "N<ns><parent><identifier>" node.
    std::string path = "U";
    for (auto s : std::views::reverse(components)) {
        char ns;
        if (s->kind == SymbolKind::Package)
            ns = 'p';
        else if (s->kind == SymbolKind::Subroutine)
            ns = 'v';
        else
            ns = 'm'; // module, InstanceBody, ClassType, etc.

        std::string next;
        next.reserve(2 + path.size() + 10 + s->name.size());
        next += 'N';
        next += ns;
        next += path;
        next += std::to_string(s->name.size());
        next += s->name;
        path = std::move(next);
    }

    return "_SV0" + path;
}

FunctionEmitter::FunctionEmitter(CodegenContext& context) : context(context), builder(context) {
}

ConstantValue FunctionEmitter::tryEval(const Expression& expr) {
    // TODO: do an actual eval, cache the result?
    if (auto cv = expr.getConstant())
        return *cv;
    return nullptr;
}

void FunctionEmitter::emitBlock(llvm::BasicBlock* bb, bool isFinished) {
    auto curBB = builder.GetInsertBlock();

    // Fall out of the current block (if necessary).
    emitBranch(bb);

    if (isFinished && bb->use_empty()) {
        delete bb;
        return;
    }

    if (curBB && curBB->getParent())
        currentFunc->insert(std::next(curBB->getIterator()), bb);
    else
        currentFunc->insert(currentFunc->end(), bb);
    builder.SetInsertPoint(bb);
}

void FunctionEmitter::emitBranch(llvm::BasicBlock* target) {
    auto curBB = builder.GetInsertBlock();
    if (!curBB || curBB->getTerminator()) {
        // If there is no insert point or the previous block is already
        // terminated, don't touch it.
    }
    else {
        // Otherwise, create a fall-through branch.
        builder.CreateBr(target);
    }
    builder.ClearInsertionPoint();
}

llvm::BasicBlock* FunctionEmitter::createBasicBlock(const llvm::Twine& name,
                                                    llvm::Function* parent) {
    return llvm::BasicBlock::Create(*context.ctx, name, parent);
}

llvm::AllocaInst* FunctionEmitter::createLocal(const VariableSymbol& var) {
    auto argTy = context.types.lower(var.getType());
    auto alloca = new llvm::AllocaInst(argTy, context.module->getDataLayout().getAllocaAddrSpace(),
                                       nullptr, var.name, localInsertPt->getIterator());
    auto [_, inserted] = locals.emplace(&var, alloca);
    SLANG_ASSERT(inserted);
    return alloca;
}

static constexpr bitmask<MethodFlags> UnimplementedFlags =
    MethodFlags::Pure | MethodFlags::Constructor | MethodFlags::InterfaceExtern |
    MethodFlags::ModportImport | MethodFlags::ModportExport | MethodFlags::DPIContext |
    MethodFlags::BuiltIn | MethodFlags::Randomize | MethodFlags::ForkJoin |
    MethodFlags::DefaultedSuperArg | MethodFlags::PrePostRandomize;

llvm::FunctionType* FunctionEmitter::createFunctionType(const SubroutineSymbol& sub) {
    SmallVector<llvm::Type*, 8> paramTypes;
    for (auto arg : sub.getArguments()) {
        if (arg->direction != ArgumentDirection::In)
            SLANG_UNIMPLEMENTED;
        paramTypes.push_back(context.types.lower(arg->getType()));
    }
    auto retTy = context.types.lower(sub.getReturnType());
    return llvm::FunctionType::get(retTy, paramTypes, /* isVarArg */ false);
}

llvm::Function* FunctionEmitter::lower(const SubroutineSymbol& sub) {
    // If we already emitted this subroutine (e.g. because it was called from another
    // subroutine first), return the existing function.
    if (auto it = context.funcMap.find(&sub); it != context.funcMap.end())
        return it->second;

    if (sub.thisVar || sub.subroutineKind != SubroutineKind::Function ||
        sub.flags.has(UnimplementedFlags) || sub.isVirtual()) {
        SLANG_UNIMPLEMENTED;
    }

    // DPI imports are lowered to external C function declarations.
    if (sub.flags.has(MethodFlags::DPIImport))
        return lowerDPIImport(sub);

    // Create the function.
    auto mangledName = mangleSubroutineName(sub);
    auto fnTy = createFunctionType(sub);
    auto fn = llvm::Function::Create(fnTy, llvm::Function::PrivateLinkage, mangledName,
                                     context.module.get());

    context.funcMap.emplace(&sub, fn);
    currentFunc = fn;
    locals.clear();

    // Create entry and return basic blocks.
    auto entryBB = createBasicBlock("entry", currentFunc);
    returnBlock = createBasicBlock("return");

    // Create a marker for inserting local variable allocations,
    // regardless of where we find them in the body.
    auto poison = llvm::PoisonValue::get(context.types.Int32Ty);
    localInsertPt = new llvm::BitCastInst(poison, context.types.Int32Ty, "allocapt", entryBB);

    // Create allocas for every formal argument.
    builder.SetInsertPoint(entryBB);
    {
        auto argIt = fn->arg_begin();
        for (auto arg : sub.getArguments()) {
            auto alloca = createLocal(*arg);
            builder.CreateStore(&*argIt, alloca);
            ++argIt;
        }
    }

    // Also pre-declare the return variable if present.
    // TODO: default initialize the result
    if (sub.returnValVar)
        returnVal = createLocal(*sub.returnValVar);
    else
        returnVal = nullptr;

    // Emit the body.
    emitStmt(sub.getBody());

    SLANG_ASSERT(!breakTarget);
    SLANG_ASSERT(!continueTarget);

    // Emit the return block. For cleanliness, we'll try to avoid emitting
    // it for simple cases.
    auto curBB = builder.GetInsertBlock();
    if (curBB) {
        SLANG_ASSERT(!curBB->getTerminator());

        // We have a valid insert point, reuse it if it is empty or there are no
        // explicit jumps to the return block.
        if (curBB->empty() || returnBlock->use_empty()) {
            returnBlock->replaceAllUsesWith(curBB);
            delete returnBlock;
            returnBlock = nullptr;
        }
        else {
            emitBlock(returnBlock);
        }
    }
    else {
        // Otherwise, if the return block is the target of a single direct
        // branch then we can just put the code in that block instead. This
        // cleans up functions which started with a unified return block.
        if (returnBlock->hasOneUse()) {
            auto bi = llvm::dyn_cast<llvm::BranchInst>(*returnBlock->user_begin());
            if (bi && bi->isUnconditional() && bi->getSuccessor(0) == returnBlock) {
                builder.SetInsertPoint(bi->getParent());
                bi->eraseFromParent();
                delete returnBlock;
                returnBlock = nullptr;
            }
        }

        // Otherwise just emit the block if it has any uses.
        if (returnBlock) {
            if (returnBlock->use_empty()) {
                delete returnBlock;
                returnBlock = nullptr;
            }
            else {
                emitBlock(returnBlock);
            }
        }
    }

    if (!returnVal)
        builder.CreateRetVoid();
    else
        builder.CreateRet(builder.CreateLoad(fn->getReturnType(), returnVal));

    // Remove the AllocaInsertPt instruction, which is just a convenience for us.
    llvm::Instruction* ptr = localInsertPt;
    localInsertPt = nullptr;
    ptr->eraseFromParent();

    // Verify the function.
    std::string errStr;
    llvm::raw_string_ostream errOS(errStr);
    if (llvm::verifyFunction(*fn, &errOS))
        SLANG_THROW(std::logic_error(errStr));

    return fn;
}

llvm::Function* FunctionEmitter::lowerDPIImport(const SubroutineSymbol& sub) {
    // Build parameter types using the DPI (C ABI compatible) mapping.
    SmallVector<llvm::Type*, 8> paramTypes;
    for (auto arg : sub.getArguments()) {
        if (arg->direction == ArgumentDirection::Out ||
            arg->direction == ArgumentDirection::InOut) {
            // Output and inout arguments are always passed by pointer.
            paramTypes.push_back(context.types.PtrTy);
        }
        else {
            SLANG_ASSERT(arg->direction == ArgumentDirection::In);
            paramTypes.push_back(context.types.lowerForDPIArg(arg->getType()));
        }
    }

    auto retTy = context.types.lowerForDPIArg(sub.getReturnType());
    auto fnTy = llvm::FunctionType::get(retTy, paramTypes, /* isVarArg */ false);

    // Declare the function with external linkage and the C calling convention
    // (which is the default) so LLVM will link it against the real C symbol at JIT time.
    auto fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage, sub.getCIdentifier(),
                                     context.module.get());

    context.funcMap.emplace(&sub, fn);
    return fn;
}

llvm::Function* FunctionEmitter::lowerDPIExport(const SubroutineSymbol& sub,
                                                std::string_view cIdent) {
    // Compute the mangled name for the internal SV function and resolve it.
    llvm::Function* svFn = nullptr;
    auto mangledName = mangleSubroutineName(sub);
    if (auto it = context.funcMap.find(&sub); it != context.funcMap.end()) {
        svFn = it->second;
    }
    else {
        svFn = context.module->getFunction(mangledName);
        if (!svFn) {
            // The SV function hasn't been emitted yet. Create a forward-declaration so
            // the thunk can reference it; lower() will fill in the body later.
            auto fnTy = createFunctionType(sub);
            svFn = llvm::Function::Create(fnTy, llvm::Function::PrivateLinkage, mangledName,
                                          context.module.get());
        }
    }

    // Build the DPI (C ABI) function type for the thunk.
    SmallVector<llvm::Type*, 8> dpiParamTypes;
    for (auto arg : sub.getArguments()) {
        if (arg->direction == ArgumentDirection::Out ||
            arg->direction == ArgumentDirection::InOut) {
            dpiParamTypes.push_back(context.types.PtrTy);
        }
        else {
            SLANG_ASSERT(arg->direction == ArgumentDirection::In);
            dpiParamTypes.push_back(context.types.lowerForDPIArg(arg->getType()));
        }
    }

    // Create the thunk with external linkage and the C identifier as name.
    auto dpiRetTy = context.types.lowerForDPIArg(sub.getReturnType());
    auto thunkFnTy = llvm::FunctionType::get(dpiRetTy, dpiParamTypes, /* isVarArg */ false);
    auto thunk = llvm::Function::Create(thunkFnTy, llvm::Function::ExternalLinkage, cIdent,
                                        context.module.get());

    // Build the thunk body: convert DPI args -> SV internal types, call svFn, convert return.
    auto entryBB = llvm::BasicBlock::Create(*context.ctx, "entry", thunk);
    builder.SetInsertPoint(entryBB);

    // TODO: review argument conversion
    SmallVector<llvm::Value*, 8> svArgs;
    auto argIt = thunk->arg_begin();
    for (auto portArg : sub.getArguments()) {
        llvm::Value* dpiVal = &*argIt++;
        const auto& argType = portArg->getType();

        if (portArg->direction == ArgumentDirection::Out ||
            portArg->direction == ArgumentDirection::InOut) {
            // Out/inout args are already pointers; forward them directly.
            svArgs.push_back(dpiVal);
            continue;
        }

        auto dpiTy = context.types.lowerForDPIArg(argType);
        auto svTy = context.types.lower(argType);
        if (dpiTy == context.types.PtrTy) {
            // Packed array argument: load from the DPI pointer and reconstruct the
            // SV internal integer representation.
            auto& ct = argType.getCanonicalType();
            const bool isFourState = ct.isFourState();
            const bitwidth_t N = ct.getBitWidth();
            if (N > 32)
                SLANG_UNIMPLEMENTED;

            if (isFourState) {
                // Layout is [1 x {i32 aval, i32 bval}] (svLogicVecVal).
                // Load the first struct from the pointer.
                auto svlvvTy = context.types.SVLogicVecValTy;
                auto svlvv = builder.CreateLoad(svlvvTy, dpiVal);
                auto aval32 = builder.CreateExtractValue(svlvv, {0});
                auto bval32 = builder.CreateExtractValue(svlvv, {1});
                // Truncate to N bits.
                auto iNTy = context.types.twoStateFor(N);
                auto valN = builder.CreateTrunc(aval32, iNTy);
                auto unkN = builder.CreateTrunc(bval32, iNTy);
                // Pack into i(2N): val in [N-1:0], unk in [2N-1:N].
                svArgs.push_back(builder.createSVInt(valN, unkN, svTy));
            }
            else {
                // Layout is [1 x i32] (svBitVecVal). Load the first word.
                auto word = builder.CreateLoad(context.types.Int32Ty, dpiVal);
                auto iNTy = context.types.twoStateFor(N);
                svArgs.push_back(builder.CreateTrunc(word, iNTy));
            }
        }
        else {
            // Scalar / predefined integer / float: may need width conversion.
            llvm::Value* val = dpiVal;
            if (svTy != dpiTy && svTy->isIntegerTy() && dpiTy->isIntegerTy()) {
                auto svBits = llvm::cast<llvm::IntegerType>(svTy)->getBitWidth();
                auto dpiBits = llvm::cast<llvm::IntegerType>(dpiTy)->getBitWidth();
                if (dpiBits > svBits)
                    val = builder.CreateTrunc(dpiVal, svTy);
                else
                    val = builder.CreateZExt(dpiVal, svTy);
            }
            svArgs.push_back(val);
        }
    }

    // Call the internal SV function.
    auto svResult = builder.CreateCall(svFn, svArgs);

    // Convert the SV return value to the DPI type and return.
    if (dpiRetTy->isVoidTy()) {
        builder.CreateRetVoid();
    }
    else {
        if (dpiRetTy == context.types.PtrTy)
            SLANG_UNIMPLEMENTED;

        auto svRetTy = context.types.lower(sub.getReturnType());
        llvm::Value* retVal = svResult;
        if (svRetTy != dpiRetTy && svRetTy->isIntegerTy() && dpiRetTy->isIntegerTy()) {
            auto svBits = llvm::cast<llvm::IntegerType>(svRetTy)->getBitWidth();
            auto dpiBits = llvm::cast<llvm::IntegerType>(dpiRetTy)->getBitWidth();
            if (dpiBits > svBits)
                retVal = builder.CreateZExt(svResult, dpiRetTy);
            else
                retVal = builder.CreateTrunc(svResult, dpiRetTy);
        }
        builder.CreateRet(retVal);
    }

    return thunk;
}

} // namespace slang::codegen

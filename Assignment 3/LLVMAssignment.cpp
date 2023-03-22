//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>


#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include "Liveness.h"
using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    std::map<unsigned int, std::set<Function *>> mResult;

    FuncPtrPass() : ModulePass(ID), mResult() {}

    bool isAddressValue(Value * inst) {
        while (true) {
            if (auto *lod = dyn_cast<LoadInst>(inst)) {
                inst = lod->getOperand(0);
            }
            else if (auto *alo = dyn_cast<AllocaInst>(inst)) {
                if (alo->getName().contains(".addr")) {
                    return true;
                }
                else {
                    return false;
                }
            }
            else {
                if (inst->getName().contains(".addr")) {
                    return true;
                }
                return false;
            }
        }
    }

    void calCallPtr(Function *func, std::set<Value *> &func_ret,
                    std::map<Value *, std::set<Function *>> &phi_func,
                    std::map<Value *, std::set<Value *>> &func_arg,
                    std::map<Value *, std::set<Value *>> &sub_store) {

        std::map<Value *, std::set<Value *>> local{};
        std::set<Value *> alloca{};
        std::map<Value *, Value *> rv_arg{};
        std::map<Value *, std::set<Value *>> if_local{};
        bool if_ret = false;

//        func->dump();
        for (BasicBlock &BB : *func) {
            std::map<Value *, std::set<Value *>> bb_local{};
            std::set<Value *> ori{};
            unsigned int arg_idx = 0;
            std::map<unsigned int, Value *> call_arg{};
            bool if_merge = false;
            // 深拷贝
            bb_local = local;
            if (BB.getName() == "if.then") {
                if_local = local;
                if_merge = true;
            }
            if (BB.getName() == "if.end" && if_ret) {
                bb_local = if_local;
                if_ret = false;
            }
            for (Instruction & I : BB) {
                if (auto *call = dyn_cast<CallBase>(&I)) {
                    unsigned int debug_col = I.getDebugLoc().getLine();
//                    if (debug_col == 84) {
//                        I.dump();
//                    }
//                    if (debug_col == 38) {
//                        I.dump();
//                    }
//                    if (debug_col == 27) {
//                        I.dump();
//                    }
//                    if (debug_col == 75) {
//                        I.dump();
//                    }
                    // 函数调用
                    if (Function * callee = call->getCalledFunction()) {
                        if (callee->isIntrinsic()) {
//                            llvm::errs() << "====wwwwww====\n";
//                            llvm::errs() << callee->getName();
                            if (callee->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
//                                llvm::errs() << "能识别就算成功\n";
//                                for (unsigned int i = 0, e = callee->arg_size(); i < e; ++i) {
//                                    llvm::errs() << i << "\n";
//                                    callee->getArg(i);
//                                }
                                Value * dst = call_arg[0];
                                Value * src = call_arg[1];
                                arg_idx = 0;
//                                llvm::errs() << "====memcpy====\n";
//                                dst->dump();
//                                src->dump();
//                                for (Value * r_dst : bb_local[dst]) {
//                                    r_dst->dump();
//                                    if (ori.find(r_dst) == ori.end()) {
//                                        continue;
//                                    }
//                                    bb_local[r_dst] = bb_local[src];
//                                    for (Value * rr_dst : bb_local[r_dst]) {
//                                        rr_dst->dump();
//                                        if (func_arg.find(rr_dst) != func_arg.end()) {
//                                            rr_dst->dump();
//                                            rv_arg[rr_dst]->dump();
//                                            sub_store[rv_arg[rr_dst]] = bb_local[src];
//                                        }
//                                    }
//                                }
                            }
                        }
                        // 自定义函数
                        if (!callee->isIntrinsic()) {
                            //记录调用结果
                            unsigned int col = I.getDebugLoc().getLine();
                            mResult[col].insert(callee);

                            // 递归处理被调函数
                            std::map<Value *, std::set<Value *>> sub_arg{};   // 函数参数
                            std::set<Value *> sub_sub_ret{};  // 返回值
                            std::map<Value *, std::set<Value *>> sub_sto{};     //函数中有store操作
                            for (unsigned int i = 0, e = callee->arg_size(); i < e; ++i) { // 遍历被调函数的参数
                                Value * opt = call->getOperand(i);
//                                opt->dump();
//                                llvm::errs() << "====arg====\n";
                                if (auto st = dyn_cast<GetElementPtrInst>(opt)) {
                                    opt = st->getOperand(0);
                                }
//                                callee->getArg(i)->dump();
                                if (func_arg.find(opt) != func_arg.end()) {
                                    // 如果参数是本函数的参数，则传递下去
//                                    func_arg[opt]->dump();
                                    sub_arg[callee->getArg(i)] = func_arg[opt];
                                }
                                else if (bb_local.find(opt) != bb_local.end()) {
//                                    opt->dump();
                                    std::set<Value *> pure{};
                                    pure = bb_local[opt];
                                    for (Value * ii : bb_local[opt]) {
//                                        ii->dump();
                                        pure.insert(ii);
                                    }
                                    pure.insert(opt);
                                    sub_arg[callee->getArg(i)] = pure;
                                }
                                else {
                                    // 如果参数是本函数的局部变量
//                                    opt->dump();
                                    sub_arg[callee->getArg(i)].insert(opt);
                                }
                            }
                            // 递归处理
                            calCallPtr(callee, sub_sub_ret, phi_func, sub_arg, sub_sto);
                            // 获取返回值
                            if (!sub_sub_ret.empty()) {
//                                sub_sub_ret->dump();
//                                call->dump();
//                                llvm::errs() << "====ret====\n";
//                                for (Value * ret_v : sub_sub_ret) {
//                                    ret_v->dump();
//                                }
                                // 将返回值保存在本函数中
                                bb_local[call]=sub_sub_ret;
                            }
                            if (!sub_sto.empty()) {
                                for (const auto& key : sub_sto) {
//                                    llvm::errs() << "====retChange====\n";
//                                    key.first->dump();
//                                    for (Value * cc : key.second) {
//                                        cc->dump();
//                                    }
                                    if (sub_arg.find(key.first) != sub_arg.end()) {
                                        for (Value * candidate : sub_arg[key.first]) {
//                                            bool merge_mode = false;
//                                            candidate->dump();
                                            if (sub_arg[key.first].size() == 1 && (bb_local.find(candidate) == bb_local.end())) {
                                                bb_local[candidate] = key.second;
                                                continue;
                                            }
                                            if (ori.find(candidate) == ori.end()) {
                                                continue;
                                            }
                                            if (auto _s = dyn_cast<Function>(candidate)) {
                                                continue;
                                            }
//                                            if (!isAddressValue(key.first) && isAddressValue(candidate)) {
//                                                merge_mode = true;
//                                            }
                                            if (bb_local.find(candidate) != bb_local.end()) {
                                                std::map<Value *, std::set<Value *>> tmp{};
                                                for (Value * oo : bb_local[candidate]) {
//                                                    oo->dump();
                                                    if (ori.find(oo) == ori.end()) {
                                                        continue;
                                                    }
                                                    if (bb_local.find(oo) != bb_local.end()) {
                                                        tmp[oo] = key.second;
                                                    }
                                                    if (alloca.find(oo) != alloca.end()) {
                                                        tmp[oo] = key.second;
                                                    }
                                                }
//                                                if (merge_mode) {
//                                                    for (const auto& sub_k : tmp) {
//                                                        for (Value * sub_v : sub_k.second) {
//                                                            bb_local[sub_k.first].insert(sub_v);
//                                                        }
//                                                    }
//                                                    for (Value * sub_v : key.second) {
//                                                        bb_local[candidate].insert(sub_v);
//                                                    }
//                                                }
//                                                else {
                                                    tmp[candidate] = key.second;
                                                    for (const auto& sub_k : tmp) {
                                                        bb_local[sub_k.first] = sub_k.second;
                                                    }
//                                                }
//                                                if (rv_arg.find(candidate) != rv_arg.end()) {
//                                                    sub_store[rv_arg[candidate]] = bb_local[candidate];
//                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // 函数指针
                    else if (Value * call_ptr = call->getCalledOperand()) {
                        // 指针是否是phi节点
                        if (auto phi = dyn_cast<PHINode>(call_ptr)) {
                            unsigned int col = I.getDebugLoc().getLine();
                            if (phi_func.count(phi) != 0) {
                                // 记录存储的phi节点中的函数
                                for (Function * candidate : phi_func[phi]) {
                                    mResult[col].insert(candidate);
                                }
                            }
                            else {
                                // 没有存储的函数
                                for (unsigned int i = 0, e = phi->getNumIncomingValues(); i < e; ++i) {
                                    Value * opt = phi->getOperand(i);
                                    // 是否在函数参数中
                                    if (func_arg.find(opt) != func_arg.end()) {
                                        unsigned int col = I.getDebugLoc().getLine();
                                        for (Value * sub_opt : func_arg[opt]) {
                                            // 是函数
                                            if (auto sub_func = dyn_cast<Function>(sub_opt)) {
                                                mResult[col].insert(sub_func);
                                            }
                                                // 是phi节点
                                            else if (auto sub_phi = dyn_cast<PHINode>(sub_opt)) {
                                                if (phi_func.count(sub_phi) != 0) {
                                                    for (Function * candidate : phi_func[sub_phi]) {
                                                        mResult[col].insert(candidate);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
//                            errs() << "CAN ---\n";
//                            I.dump();
//                            phi->dump();
//                            call->dump();
//                            call_ptr->dump();
//                            errs() << "--- END\n";
                            // 递归处理被调函数
                            for (Function * sub_func : phi_func[phi]) {
                                std::map<Value *, std::set<Value *>> sub_arg{};
                                std::set<Value *> sub_sub_ret{};
                                std::map<Value *, std::set<Value *>> sub_sto{};
                                for (unsigned int i = 0, e = sub_func->arg_size(); i < e; ++i) {
                                    Value * opt = call->getOperand(i);
                                    if (func_arg.find(opt) != func_arg.end()) {
                                        sub_arg[sub_func->getArg(i)] = func_arg[opt];
                                    }
                                    else {
                                        sub_arg[sub_func->getArg(i)].insert(opt);
                                    }
//                                    sub_func->getArg(i)->dump();
//                                    opt->dump();
                                }
                                calCallPtr(sub_func, sub_sub_ret, phi_func, sub_arg, sub_sto);
                                if (!sub_sub_ret.empty()) {
//                                    sub_sub_ret->dump();
                                    bb_local[call] = sub_sub_ret;
                                }
                            }
                        }
                            // 指针是否在函数参数中
                        else if (func_arg.find(call_ptr) != func_arg.end()) {
                            // 是否是phi节点
                            for (Value * suspend : func_arg[call_ptr]) {
                                if (auto phi = dyn_cast<PHINode>(suspend)) {
                                    if (phi_func.count(phi) != 0) {
                                        unsigned int col = I.getDebugLoc().getLine();
                                        for (Function * candidate : phi_func[phi]) {
                                            mResult[col].insert(candidate);
                                        }
                                    }
                                }
                                    // 是函数
                                else if (auto candidate = dyn_cast<Function>(suspend)) {
                                    unsigned int col = I.getDebugLoc().getLine();
                                    mResult[col].insert(candidate);

                                    // 递归处理
                                    std::map<Value *, std::set<Value *>> sub_arg{};
                                    std::set<Value *> sub_sub_ret{};
                                    std::map<Value *, std::set<Value *>> sub_sto{};
                                    for (unsigned int i = 0, e = candidate->arg_size(); i < e; ++i) {
                                        Value * opt = call->getOperand(i);
//                                    candidate->getArg(i)->dump();
                                        if (func_arg.find(opt) != func_arg.end()) {
                                            sub_arg[candidate->getArg(i)] = func_arg[opt];
//                                        func_arg[opt]->dump();
                                        }
                                        else {
                                            sub_arg[candidate->getArg(i)].insert(opt);
//                                        opt->dump();
                                        }
                                    }
                                    calCallPtr(candidate, sub_sub_ret, phi_func, sub_arg, sub_sto);
                                    if (!sub_sub_ret.empty()) {
//                                    sub_sub_ret->dump();
                                        bb_local[call] = sub_sub_ret;
                                    }
                                }
                            }
                        }
                        // 是否之前处理过
                        /// !TODO 处理local
                        else if (bb_local.find(call_ptr) != bb_local.end()) {
                            unsigned int col = I.getDebugLoc().getLine();
//                            call_ptr->dump();
                            bool have_func = false;
                            for (Value * opt : bb_local[call_ptr]) {
//                                opt->dump();
                                if (auto sub_func = dyn_cast<Function>(opt)) {
                                    have_func = true;
                                    mResult[col].insert(sub_func);
                                    std::map<Value *, std::set<Value *>> sub_arg{};
                                    std::set<Value *> sub_sub_ret{};
                                    std::map<Value *, std::set<Value *>> sub_sto{};
                                    for (unsigned int i = 0, e = sub_func->arg_size(); i < e; ++i) {
                                        Value * sub_opt = call->getOperand(i);
                                        if (func_arg.find(opt) != func_arg.end()) {
                                            // 如果参数是本函数的参数，则传递下去
                                            sub_arg[sub_func->getArg(i)] = func_arg[sub_opt];
                                        }
                                        /// !TODO 基本块内和函数参数
                                        else if (bb_local.find(sub_opt) != bb_local.end()) {
//                                            sub_opt->dump();
                                            std::set<Value *> pure{};
                                            pure = bb_local[sub_opt];
                                            for (Value * ii : bb_local[sub_opt]) {
//                                                ii->dump();
                                                if (bb_local.find(ii) != bb_local.end()) {
                                                    for (Value * vv : bb_local[ii]) {
//                                                        vv->dump();
                                                        pure.insert(vv);
                                                    }
                                                }
                                            }
                                            sub_arg[sub_func->getArg(i)] = pure;
                                        }
                                        else{
                                            // 如果参数是本函数的局部变量
                                            sub_arg[sub_func->getArg(i)].insert(sub_opt);
                                        }
                                    }
                                    calCallPtr(sub_func, sub_sub_ret, phi_func, sub_arg, sub_sto);
                                    if (!sub_sub_ret.empty()) {
                                        for (Value * ret_i : sub_sub_ret) {
                                            bb_local[call].insert(ret_i);
                                        }
                                    }
                                }
                                else if (auto sub_phi = dyn_cast<PHINode>(opt)) {
                                    if (phi_func.find(sub_phi) != phi_func.end()) {
                                        for (Function * candidate : phi_func[sub_phi]) {
                                            mResult[col].insert(candidate);
                                        }
                                    }
                                }
                                else if (bb_local.find(opt) != bb_local.end() && !have_func) {
//                                    opt->dump();
                                    for (Value * candidate : bb_local[opt]) {
//                                        candidate->dump();
                                        if (auto real_call = dyn_cast<Function>(candidate)) {
                                            mResult[col].insert(real_call);
                                        }
                                    }
                                }
                            }
//                            sub_ret[call] = sub_ret[call_ptr];
                        }
                    }
                }
                // return指令
                else if (auto *ret = dyn_cast<ReturnInst>(&I)) {
                    unsigned int col = I.getDebugLoc().getLine();
//                    if (col == 20) {
//                        I.dump();
//                    }
                    Value * opt = ret->getReturnValue();

                    // 设置返回值
                    if (func_arg.find(opt) != func_arg.end()) {
                        func_ret = func_arg[opt];
                    }
                    else if (bb_local.find(opt) != bb_local.end()) {
                        func_ret = bb_local[opt];
                    }
//                    if (sub_ret.find(opt) != sub_ret.end()) {
//                        for (Value * ret_opt : sub_ret[opt]) {
//                            if (auto sub_func = dyn_cast<Function>(ret_opt)) {
//                                mResult[col].insert(sub_func);
//                            }
//                            else if (auto sub_phi = dyn_cast<PHINode>(ret_opt)) {
//                                if (phi_func.find(sub_phi) != phi_func.end()) {
//                                    for (Function * candidate : phi_func[sub_phi]) {
//                                        mResult[col].insert(candidate);
//                                    }
//                                }
//                            }
//                        }
//                    }
                }
                // phi节点
                else if (auto *phi = dyn_cast<PHINode>(&I)) {
//                    phi->dump();
                    for (unsigned int i = 0, phi_count = phi->getNumIncomingValues(); i < phi_count; ++i) {
                        if (Value * opt = phi->getOperand(i)) {
//                            opt->dump();
                            // 操作数为函数，保存
                            if (auto callee = dyn_cast<Function>(opt)) {
                                phi_func[phi].insert(callee);
                            }
                                // 操作数为phi节点，扩展保存
                            else if (auto sub_phi = dyn_cast<PHINode>(opt)) {
                                for (Function * candidate : phi_func[sub_phi]) {
                                    phi_func[phi].insert(candidate);

                                }
                            }
                            // 操作数为函数参数
                            else if (func_arg.find(opt) != func_arg.end()) {
                                // 函数，保存
                                for (Value * suspend : func_arg[opt]) {
                                    if (auto candidate = dyn_cast<Function>(suspend)) {
                                        phi_func[phi].insert(candidate);
                                    }
                                    // phi节点，扩展保存
                                    else if (auto sub_phi = dyn_cast<PHINode>(suspend)) {
                                        for (Function * candidate : phi_func[sub_phi]) {
                                            phi_func[phi].insert(candidate);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                else if (auto *sto = dyn_cast<StoreInst>(&I)) {
                    Value * src = sto->getOperand(0);
                    Value * dst = sto->getOperand(1);
                    if (auto st = dyn_cast<GetElementPtrInst>(dst)) {
                        dst = st->getOperand(0);
                    }
                    if (auto st = dyn_cast<GetElementPtrInst>(src)) {
                        src = st->getOperand(0);
                    }
//                    llvm::errs() << "-----------------\n";
//                    sto->dump();
//                    src->dump();
//                    dst->dump();
                    ori.insert(src);
                    ori.insert(dst);
                    if (auto *raw_call = dyn_cast<Function>(src)) {
                        bool alloc_flag = false;
                        if (bb_local.find(dst) != bb_local.end()) {
                            for (Value * candidate : bb_local[dst]) {
//                                candidate->dump();
                                if (ori.find(candidate) == ori.end()) {
                                    continue;
                                }
                                if (bb_local.find(candidate) != bb_local.end()) {
                                    bb_local[candidate] = std::set<Value *>{raw_call};
                                }
                                if (alloca.find(candidate) != alloca.end()) {
                                    bb_local[candidate] = std::set<Value *>{raw_call};
//                                    llvm::errs() << "ok\n";
                                    alloc_flag = true;
                                }
                            }
                        }
                        if (!alloc_flag) {
                            bb_local[dst] = std::set<Value *>{raw_call};
//                            dst->dump();
//                            raw_call->dump();
                        }
                    }
                    else if (func_arg.find(src) != func_arg.end()) {
//                        for (unsigned int i = 0, e = func->arg_size(); i < e; ++i) {
//                            func->getArg(i)->dump();
//                        }
//                        for (Value * fa : func_arg[src]) {
//                            fa->dump();
//                        }
                        bb_local[dst] = func_arg[src];
                        rv_arg[dst] = src;
                    }
                    else if (bb_local.find(src) != bb_local.end()) {
                        std::set<Value *> pure{};
                        Value * mid = nullptr;
                        bool merge_mode = false;
//                        bb_local[dst] = std::set<Value *>{};
                        if (!isAddressValue(src) && isAddressValue(dst)) {
                            merge_mode = true;
                        }
//                        llvm::errs() << "====candidate====\n";
                        for (Value * candidate : bb_local[src]) {
//                            candidate->dump();
                            if (pure.find(candidate) == pure.end()) {
                                pure.insert(candidate);
                            }
                        }
                        std::map<Value *, std::set<Value *>> tmp{};
                        if (bb_local.find(dst) != bb_local.end()) {
                            for (Value * candidate : bb_local[dst]) {
//                                llvm::errs() << "====ssss====\n";
//                                candidate->dump();
                                if (ori.find(candidate) == ori.end()) {
                                    continue;
                                }
                                if (pure.find(candidate) != pure.end()) {
                                    continue;
                                }
                                if (bb_local.find(candidate) != bb_local.end()) {
                                    tmp[candidate] = pure;
                                }
                                if (alloca.find(candidate) != alloca.end()) {
                                    tmp[candidate] = pure;
                                }
                                if (rv_arg.find(candidate) != rv_arg.end()) {
//                                    rv_arg[candidate]->dump();
                                    sub_store[rv_arg[candidate]] = pure;
                                }
                            }
                        }
                        if (merge_mode) {
                            for (const auto& sub_k : tmp) {
                                for (Value * sub_v : sub_k.second) {
                                    bb_local[sub_k.first].insert(sub_v);
                                }
                            }
                            for (Value * sub_v : pure) {
                                bb_local[dst].insert(sub_v);
                            }
                        }
                        else {
                            for (const auto& sub_k : tmp) {
                                bb_local[sub_k.first] = sub_k.second;
                            }
                            bb_local[dst] = pure;
                        }
                    }
                    else {
                        bb_local[dst] = std::set<Value *>{src};
                    }
                }
                else if (auto *lod = dyn_cast<LoadInst>(&I)) {
                    Value * src = lod->getPointerOperand();
                    if (auto st = dyn_cast<GetElementPtrInst>(src)) {
                        src = st->getOperand(0);
                    }
//                    llvm::errs() << "-----------------\n";
//                    lod->dump();
//                    src->dump();
                    ori.insert(src);
                    if (bb_local.find(src) != bb_local.end()) {
                        bb_local[lod] = bb_local[src];
                        if (alloca.find(src) != alloca.end()) {
                            bb_local[lod].insert(src);
                        }
                    }
                    else {
                        bb_local[lod] = std::set<Value *>{src};
                    }
                }
                else if (auto *alo = dyn_cast<AllocaInst>(&I)) {
                    alloca.insert(alo);
                }
                else if (auto *bic = dyn_cast<BitCastInst>(&I)) {
                    Value * src = bic->getOperand(0);
                    if (auto st = dyn_cast<GetElementPtrInst>(src)) {
                        src = st->getOperand(0);
                    }
//                    llvm::errs() << "-----------------\n";
//                    src->dump();
                    ori.insert(src);
                    call_arg[arg_idx] = bic;
                    arg_idx += 1;
                    if (bb_local.find(src) !=  bb_local.end()) {
                        bb_local[bic] = bb_local[src];
                    }
                    else {
                        bb_local[bic] = std::set<Value *>{src};
                    }
                }
                else if (auto *bri = dyn_cast<BranchInst>(&I)) {
//                    llvm::errs() << "====br===\n";
//                    bri->dump();
//                    llvm::errs() << bri->getOperand(0)->getName() << "\n";
//                    llvm::errs() << BB.getName() << "\n";
                    if (bri->getOperand(0)->getName() == "return" && BB.getName() == "if.then") {
//                        llvm::errs() << "ok\n";
                        if_ret = true;
                    }
                }
//                else if (auto *gep = dyn_cast<GetElementPtrInst>(&I)) {
//                    Value * src = gep->getOperand(0);
//                    gep->dump();
//                    src->dump();
//                    bb_local[gep] = bb_local[src];
//                }
            }
            // 合并local
//            llvm::errs() << "????????????????????\n";
            for (const auto& key : bb_local) {
//          llvm::errs() << "++++++++++++\n";
//          key.first->dump();
                for(Value * it : key.second) {
                    local[key.first].insert(it);
//                    it->dump();
                }
            }
        }
    }

    void display() {
        for (auto &it : mResult) {
            errs() << it.first << " : ";
            bool comma = false;
            for (Function * func : it.second) {
                if (comma) {
                    errs() << ", ";
                }
                errs() << func->getName();
                comma = true;
            }
            errs() << "\n";
        }
    }

    bool runOnModule(Module &M) override {

//        M.dump();
        for (Function &func : M) {
            // map phi -> functions
            std::map<Value *, std::set<Function *>> phi_func{};
            // save the arg of callee
            std::map<Value *, std::set<Value *>> func_arg{};
            std::map<Value *, std::set<Value *>> sub_store{};
            // save the return value
            std::set<Value *> ret;
            if (!func.isIntrinsic()) {
                calCallPtr(&func, ret, phi_func, func_arg, sub_store);
            }
        }

        display();
        return false;
    }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
#if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
#endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
//#ifndef NDEBUG
//   system("pause");
//#endif
}


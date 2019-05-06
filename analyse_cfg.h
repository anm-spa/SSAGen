//
//  analyse_cfg.h
//  SSAGen
//
//  Created by Abu Naser Masud on 2019-01-11.
//  Copyright © 2019 Abu Naser Masud. All rights reserved.
//

#ifndef analyse_cfg_h
#define analyse_cfg_h

#include <algorithm>
#include "dataFlowAnalysis.h"
#include <ctime>
#include <chrono>

using namespace std::chrono;
using namespace llvm;
using namespace clang;

class CFGAnalysis
{
private:
    std::unique_ptr<clang::CFG> cfg;
    clang::ASTContext &context;
    std::set<unsigned> vars;
    std::map<unsigned,VarInfoInBlock> BlockToVars;
    std::set<unsigned> gDefs, gRefs;
    VarInfoT varInfo;
    DFAnalysis df;
    unsigned debugL;
    
public:
    CFGAnalysis(ASTContext &C):context(C){}
   // CFGAnalysis(std::unique_ptr<clang::CFG> &&CFG,ASTContext &C);
    CFGAnalysis(std::unique_ptr<clang::CFG> &&CFG, ASTContext &C, unsigned dl);
    void dataflow_analysis();
    void blockDefRefInfo(CFGBlock *B);
    void WalkThroughBasicBlockStmts(CFGBlock *B);
    void GetVarsFromStmt(const Stmt *S,VarInfoInBlock &varBlock);
    bool WalkThroughExpr(const Expr * expr, std::set<unsigned> &Refs, std::set<unsigned> &globals);
    void VisitBinaryOp(const BinaryOperator *B,std::set<unsigned> &Defs, std::set<unsigned> &Refs, std::set<unsigned> &globalDefs,std::set<unsigned> &globalRefs);
    std::string findVar(const Expr *E);
    bool isGlobalVar(const Expr *E);
    const Expr *stripCasts(const Expr *Ex);
    std::set<unsigned> getVars();
    std::string getVarName(unsigned v);
    std::set<CFGBlock *> getDefsOfVar(unsigned v);
    void exportPhiResults(std::map<unsigned,std::set<unsigned> > &phiNodes);
};

CFGAnalysis::CFGAnalysis(std::unique_ptr<clang::CFG> &&CFG, ASTContext &C, unsigned dl):context(C)
{
    //context=clang::ASTContext(C);
    cfg=std::move(CFG);
    varInfo=VarInfoT();
    debugL=dl;
    for (auto *Block : *cfg){
        WalkThroughBasicBlockStmts(Block);
    }
    CFGBlock &eB=cfg->getEntry();
    
    // Only some vars are defined at the start node
    // BlockToVars[eB.getBlockID()].BlockDefs.insert(gDefs.begin(),gDefs.end());
    
    // Alternative Defs for equivalent results with DF (Assuming all vars are defined at the start node)
      BlockToVars[eB.getBlockID()].BlockDefs.insert(vars.begin(),vars.end());
    if(debugL>1){
        for (auto *B : *cfg){
          blockDefRefInfo(B);
        }
    }
}

void CFGAnalysis::dataflow_analysis()
{
    df=DFAnalysis(cfg, vars,varInfo,debugL);
    df.computeFixpoint(vars,BlockToVars);
    
    for (auto *block : *cfg){
        for(CFGBlock::const_succ_iterator I = block->succ_begin(), F = block->succ_end(); I != F; ++I)
        {
            if(!(*I)) continue; //ignore unreachable block
            unsigned eID=df.edgeID(block->getBlockID(),(*I)->getBlockID());
            if(debugL>0)
              llvm::errs()<< "Edge ("<<block->getBlockID()<<", "<<(*I)->getBlockID()<<") is visited "<<df.numEdgeVisit[eID]<<" times\n";
        }
    }
    
    if(debugL>2){
    for (auto *block : *cfg)
       df.debug_print(block->getBlockID(),vars);
    for(auto v:vars)
       llvm::errs()<<v<<" mapped to "<<varInfo.mapsfrom(v)<<"\n";
    }
    
    if(debugL>1){
       df.printDFValues_withDebug(cfg,vars,BlockToVars);
       df.printPhiNodes(cfg,vars);
    }
    else
       df.printDFValues(cfg,vars,BlockToVars);
}

void CFGAnalysis::blockDefRefInfo(CFGBlock *B)
{
    llvm::errs() << "Block :"<<B->getBlockID()<<"\n";
    llvm::errs() << "Defs :";
    if(!BlockToVars[B->getBlockID()].BlockDefs.empty())
        for (auto it=BlockToVars[B->getBlockID()].BlockDefs.begin(); it!=BlockToVars[B->getBlockID()].BlockDefs.end(); ++it)
            llvm::errs() << varInfo.mapsfrom(*it)<<" ("<<*it<<") ";
    llvm::errs() << '\n';
    
    llvm::errs() << "Refs :";
    if(!BlockToVars[B->getBlockID()].BlockRefs.empty())
        for (auto it=BlockToVars[B->getBlockID()].BlockRefs.begin(); it!=BlockToVars[B->getBlockID()].BlockRefs.end(); ++it)
            llvm::errs() << varInfo.mapsfrom(*it)<<" ";
    llvm::errs() << '\n';
}

void CFGAnalysis::WalkThroughBasicBlockStmts(CFGBlock *B)
{
    
    // llvm::errs()<<"Block "<<B->getBlockID()<<"\n";
    VarInfoInBlock VarsB;
    for ( auto &Bi : *B) {
        std::set<unsigned> Def,Ref;
        switch (Bi.getKind()) {
            case CFGElement::Statement: {
                CFGStmt* S = reinterpret_cast<CFGStmt*>(&Bi);
                GetVarsFromStmt(S->getStmt(),VarsB);
                break;
            }
            default:
                break;
        }
    }
    vars.insert(VarsB.BlockDefs.begin(),VarsB.BlockDefs.end());
    vars.insert(VarsB.BlockRefs.begin(),VarsB.BlockRefs.end());
    BlockToVars[B->getBlockID()]=VarsB;
}

void CFGAnalysis::GetVarsFromStmt(const Stmt *S,VarInfoInBlock &varBlock)
{
    std::set<unsigned> Defs, Refs,globalDefs,globalRefs;
    if (const clang::BinaryOperator *bop=dyn_cast<clang::BinaryOperator>(S))
        VisitBinaryOp(bop,Defs,Refs,globalDefs,globalRefs);
    else if (const clang::UnaryOperator *uop=dyn_cast<clang::UnaryOperator>(S)){
        if(uop->isIncrementDecrementOp())
        {
            const clang::Expr *subexp=uop->getSubExpr()->IgnoreImplicit();
            std::set<unsigned> temp;
            WalkThroughExpr(subexp,temp,globalDefs);
            //Probably it can be made efficient
            Defs.insert(temp.begin(),temp.end());
            Refs.insert(temp.begin(),temp.end());
            globalRefs.insert(globalDefs.begin(),globalDefs.end());
            
        }
    }
    if (const CallExpr *call = dyn_cast<CallExpr>(S)) {
        for(unsigned i=0;i<call->getNumArgs();i++)
        {
            const Expr *expr = call->getArg(i);
            std::string s("scanf");
            const FunctionDecl * fd=call->getDirectCallee();
            if((fd) && (fd->getNameAsString()==s)){
                if(const clang::UnaryOperator *U=dyn_cast<clang::UnaryOperator>(expr))
                {
                    const clang::Expr *subexp=U->getSubExpr()->IgnoreImplicit();
                    WalkThroughExpr(subexp,Defs,globalDefs);
                }
            }
            else
            {
                WalkThroughExpr(call->getArg(i),Refs,globalRefs);
            }
        }
    }
    if (const DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
        for (const auto *DI : DS->decls()) {
            const auto *V = dyn_cast<VarDecl>(DI);
            if (!V) continue;
            if (const Expr *E = V->getInit())
            {
                WalkThroughExpr(E,Refs,globalRefs);
                unsigned numVar=varInfo.mapsto(V->getNameAsString());
                Defs.insert(numVar);
            }
            
        }
    }
    
    if(const ReturnStmt *rtst = dyn_cast<ReturnStmt>(S)) {
        if(const Expr *retexpr=rtst->getRetValue()){
            //const Expr *retexpr=rtst->getRetValue()->IgnoreImplicit();
            WalkThroughExpr(retexpr,Refs,globalRefs);
        }
    }
    if (const IfStmt *ifstmt = dyn_cast<IfStmt>(S)) {
        const Expr *ifexp=ifstmt->getCond();
        std::set<std::string> Ref;
        if(ifexp)
            WalkThroughExpr(ifexp->IgnoreImplicit(),Refs,globalRefs);
    }
    /*else if (ForStmt *forstmt = dyn_cast<ForStmt>(st))
     {
     Expr *forexp=forstmt->getCond();
     if(forexp) traverse_subExpr(forexp->IgnoreImplicit());
     }
     else if(WhileStmt *whilestmt = dyn_cast<WhileStmt>(st))
     {
     Expr *whileexp=whilestmt->getCond();
     if(whileexp) traverse_subExpr(whileexp->IgnoreImplicit());
     }*/
    
    
    varBlock.insertVarInfo(Defs,Refs);
    gDefs.insert(globalDefs.begin(),globalDefs.end());
    gRefs.insert(globalRefs.begin(),globalRefs.end());
}

bool CFGAnalysis::WalkThroughExpr(const Expr * expr, std::set<unsigned> &Refs, std::set<unsigned> &globals)
{
    if(!expr) return false;
    const Expr *exp=stripCasts(expr);
    if(exp->isIntegerConstantExpr(context,NULL)) return 1;
    if(const clang::DeclRefExpr *dexpr=dyn_cast<clang::DeclRefExpr>(exp))
    {
        if(const auto DV=dyn_cast<VarDecl>(dexpr->getDecl()))
        {
            unsigned numVar=varInfo.mapsto(DV->getNameAsString());
            Refs.insert(numVar);
            if(DV->hasLinkage()) globals.insert(numVar);
            return 1;
        }
    }
    
    /*if(clang::UnaryOperator *uop=dyn_cast<clang::UnaryOperator>(exp))
     {
     clang::Expr *subexp=uop->getSubExpr()->IgnoreImplicit();
     traverse_subExpr(subexp);
     return true;
     }*/
    
    if(const BinaryOperator *bop=dyn_cast<BinaryOperator>(exp))
    {
        const Expr *lhs=bop->getLHS();
        const Expr *rhs=bop->getRHS();
        WalkThroughExpr(lhs->IgnoreImplicit(),Refs,globals);
        WalkThroughExpr(rhs->IgnoreImplicit(),Refs,globals);
        return 1;
    }
    return 0;
}

void CFGAnalysis::VisitBinaryOp(const BinaryOperator *B,std::set<unsigned> &Defs, std::set<unsigned> &Refs, std::set<unsigned> &globalDefs,std::set<unsigned> &globalRefs) {
    
    switch(B->getOpcode()){
        case BO_MulAssign:
        case BO_DivAssign:
        case BO_RemAssign:
        case BO_AddAssign:
        case BO_SubAssign:
        case BO_ShlAssign:
        case BO_ShrAssign:
        case BO_AndAssign:
        case BO_OrAssign:
        case BO_XorAssign: { std::string var=findVar(B->getLHS());
            unsigned numVar=varInfo.mapsto(var);
            Defs.insert(numVar);
            Refs.insert(numVar);
            if(isGlobalVar(B->getLHS()))
                globalDefs.insert(numVar);
            WalkThroughExpr(B->getRHS(),Refs,globalRefs);
            break;
        }
        case BO_Assign:    { std::string var=findVar(B->getLHS());
            unsigned numVar=varInfo.mapsto(var);
            Defs.insert(numVar);
            if(isGlobalVar(B->getLHS()))
                globalDefs.insert(numVar);
            WalkThroughExpr(B->getRHS(),Refs,globalRefs);
            break;
        }
        default:{            WalkThroughExpr(B->getLHS(),Refs,globalRefs);
            WalkThroughExpr(B->getRHS(),Refs,globalRefs);
            break;
        }
    }
}

std::string CFGAnalysis::findVar(const Expr *E) {
    if (const auto *DRE =dyn_cast<DeclRefExpr>(stripCasts(E)))
        return DRE->getDecl()->getNameAsString ();
    else
    {   llvm::errs()<<"Not a Valid Variable\n";
        E->dump();
        return "not_a_valid_variable";}
}
bool CFGAnalysis::isGlobalVar(const Expr *E) {
    if (const auto *DRE =dyn_cast<DeclRefExpr>(stripCasts(E)))
        if(DRE->getDecl()->hasLinkage()) return true;
    return false;
}

const Expr *CFGAnalysis::stripCasts(const Expr *Ex) {
    while (Ex) {
        Ex = Ex->IgnoreParenNoopCasts(context);
        if (const auto *CE = dyn_cast<CastExpr>(Ex)) {
            if (CE->getCastKind() == CK_LValueBitCast) {
                Ex = CE->getSubExpr();
                continue;
            }
        }
        break;
    }
    return Ex;
}

std::set<unsigned> CFGAnalysis::getVars()
{
    return vars;
}

std::string CFGAnalysis::getVarName(unsigned v)
{
    return varInfo.mapsfrom(v);
}

std::set<CFGBlock *> CFGAnalysis::getDefsOfVar(unsigned v)
{
    std::set<CFGBlock *> result=std::set<CFGBlock *>();
    for (auto *block : *cfg){
        if(BlockToVars[block->getBlockID()].isDef(v))
            result.insert(block);
    }
    return result;
}

void CFGAnalysis::exportPhiResults(std::map<unsigned,std::set<unsigned> > &pNodes)
 {
     df.exportResults(cfg, vars, pNodes);
 }

#endif /* analyse_cfg_h */

/****************************************************************/
/*          All rights reserved (it will be changed)            */
/*          masud.abunaser@mdh.se                               */
/****************************************************************/

#include "clang/Driver/Options.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Sema/Sema.h"
#include "clang/Basic/LangOptions.h"
#include "clang/AST/AST.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Analysis/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/AnalysisDeclContext.h"

#include <memory>
#include <ctime>
#include <sstream>
#include <string>
#include "analyse_cfg.h"
#include <algorithm>
#include <chrono>

using namespace std;
using namespace std::chrono;

using namespace llvm;
using namespace clang::driver;
using namespace clang::tooling;
using namespace clang;

#include "commandOptions.h"

typedef high_resolution_clock Clock;
typedef Clock::time_point ClockTime;

//#include "clang/Rewrite/Core/Rewriter.h"

void printExecutionTime(ClockTime start_time, ClockTime end_time)
{
    auto execution_time_ns = duration_cast<nanoseconds>(end_time - start_time).count();
    auto execution_time_ms = duration_cast<microseconds>(end_time - start_time).count();
    auto execution_time_sec = duration_cast<seconds>(end_time - start_time).count();
    auto execution_time_min = duration_cast<minutes>(end_time - start_time).count();
    auto execution_time_hour = duration_cast<hours>(end_time - start_time).count();
    
    llvm::errs() << "\nExecution Time: ";
    if(execution_time_hour > 0)
        llvm::errs() << "" << execution_time_hour << " Hours, ";
    if(execution_time_min > 0)
        llvm::errs() << "" << execution_time_min % 60 << " Minutes, ";
    if(execution_time_sec > 0)
        llvm::errs() << "" << execution_time_sec % 60 << " Seconds, ";
    if(execution_time_ms > 0)
        llvm::errs() << "" << execution_time_ms % long(1E+3) << " MicroSeconds, ";
    if(execution_time_ns > 0)
        llvm::errs() << "" << execution_time_ns % long(1E+6) << " NanoSeconds, ";
}

class CFGVisitor : public RecursiveASTVisitor<CFGVisitor> {
public:
    CFGVisitor(ASTContext &C,unsigned dl) : context(C) {_dl=dl;}
    
    void TraverseCFG(std::unique_ptr<CFG> &cfg)
    {
    }
    
    void compare_results(FunctionDecl *f,CFGAnalysis *cfgAnal,std::map<unsigned,std::set<unsigned> > &phiNodesDF,std::map<unsigned,std::set<unsigned> > &pNodes)
    {
        const Decl* D=static_cast<Decl *>(f);
        AnalysisDeclContextManager  *analDeclCtxMgr=new AnalysisDeclContextManager(context);
        AnalysisDeclContext  analDeclCtx(analDeclCtxMgr,D);
        llvm::errs()<<"\n\nComparing Phi Functions";
        bool status=false;
        for (auto *block : *(analDeclCtx.getCFG())){
            unsigned bID=block->getBlockID();
            if(block->pred_size()>1)
            {
                if(!(phiNodesDF[bID]==pNodes[bID])) {
                    llvm::errs()<<"\nBlock "<<bID<<" has different Phi functions";
                    status=true;
                }
            }
        }
        if(!status) llvm::errs()<<": no difference found!!!\n";
    }
   
    void calculate_DF(std::map<unsigned, std::set<unsigned>> &DF,DominatorTree &domTree,DomTreeNode *node)
    {
           for(auto z:node->getChildren())
               calculate_DF(DF,domTree,z);
        DF[node->getBlock()->getBlockID()]=std::set<unsigned>();
        CFGBlock *B = idToBlock[node->getBlock()->getBlockID()];
        for(auto i=B->succ_begin(), e=B->succ_end();i!=e;i++)
        {
            if(!domTree.DT->getNode(*i)) continue;
            CFGBlock *b=domTree.DT->getNode(*i)->getIDom()->getBlock();
            if(b->getBlockID()!=node->getBlock()->getBlockID())
                DF[node->getBlock()->getBlockID()].insert((*i)->getBlockID());
        }
        
        for(auto z:node->getChildren())
        {
            for(auto y:DF[z->getBlock()->getBlockID()])
            {
                CFGBlock *Y = idToBlock[y];
                if(!domTree.DT->getNode(Y)) continue;
                CFGBlock *idom=domTree.DT->getNode(Y)->getIDom()->getBlock();
                if(idom->getBlockID()!=node->getBlock()->getBlockID()){
                    DF[node->getBlock()->getBlockID()].insert(Y->getBlockID());
                }
                
            }
        } // outer for
    }
    
    void computePhifunctions(FunctionDecl *f, CFGAnalysis *cfgAnal,std::map<unsigned,std::set<unsigned> > &pNodes)
    {
        // Alternative method based on dominator tree
        const Decl* D=static_cast<Decl *>(f);
        AnalysisDeclContextManager  *analDeclCtxMgr=new AnalysisDeclContextManager(context);
        if(AnalysisDeclContext  *analDeclCtx=analDeclCtxMgr->getContext(D)){
        DominatorTree domTree;
           
        domTree.buildDominatorTree(*analDeclCtx);
          
        //blockIdMap(analDeclCtx.getCFG());
        for (auto *B : *(analDeclCtx->getCFG()))
            idToBlock[B->getBlockID()]=B;
       /// domTree.dump();
        
        std::map<unsigned, std::set<unsigned>> DF;
        
        for (auto *block : *(analDeclCtx->getCFG())){
            DF[block->getBlockID()]=std::set<unsigned>();
        }
        calculate_DF(DF,domTree,domTree.getRootNode());
        
        if(_dl>2)
          for (auto *block : *(analDeclCtx->getCFG())){
              llvm::errs()<<"DF of "<<block->getBlockID()<<": ";
             for(auto i=DF[block->getBlockID()].begin(), e=DF[block->getBlockID()].end();
                i!=e;i++)
                 llvm::errs()<<*i<<" ";
            llvm::errs()<<"\n";
        }
        
        std::map<unsigned, std::map< unsigned,unsigned>> DF_number;
        
        unsigned iterCount=0;
        std::map<unsigned,unsigned> hasAlready, work;
        std::map<unsigned, std::set<unsigned> > phiNodes;
        for (auto *block : *(analDeclCtx->getCFG())){
            hasAlready[block->getBlockID()]=0;
            work[block->getBlockID()]=0;
            phiNodes[block->getBlockID()]=std::set<unsigned>();
        }
        for (auto *block : *(analDeclCtx->getCFG())){
            if(block->pred_size()>1)
            {
                for(auto v:cfgAnal->getVars())
                    DF_number[block->getBlockID()][v]=0;
            }
        }
        
        std::queue<unsigned> W;
        for(auto v:cfgAnal->getVars())
        {
            iterCount = iterCount+1;
            std::set<CFGBlock *> bList=cfgAnal->getDefsOfVar(v);
            for(auto *block: bList)
            {
                work[block->getBlockID()]=iterCount;
                W.push(block->getBlockID());
            }
            W.push(analDeclCtx->getCFG()->getEntry().getBlockID());
            while(!W.empty())
            {
                unsigned x=W.front();
                W.pop();
                for(auto y:DF[x])
                {
                    DF_number[y][v]++;
                    if(hasAlready[y]<iterCount)
                    {
                        if(_dl>2)
                           llvm::errs()<<y << " needs phi for "<<cfgAnal->getVarName(v)<<"\n";
                        phiNodes[y].insert(v);
                        pNodes[y].insert(v);
                        hasAlready[y]=iterCount;
                        if(work[y]<iterCount)
                        {
                            work[y]=iterCount;
                            W.push(y);
                        }
                    }
                }
            }
        }
        }
    }

    
    void computePhifunctions2(FunctionDecl *f, CFGAnalysis *cfgAnal)
    {
        // Alternative method based on dominator tree
        const Decl* D=static_cast<Decl *>(f);
        AnalysisDeclContextManager  *analDeclCtxMgr=new AnalysisDeclContextManager(context);
        AnalysisDeclContext  analDeclCtx(analDeclCtxMgr,D);
        DominatorTree domTree;
        domTree.buildDominatorTree(analDeclCtx);
       
        std::map<unsigned, std::set<unsigned>> DF,DF2;
        std::map<CFGBlock *, std::set<CFGBlock *>> DF1;
        
        std::map<unsigned, std::map< unsigned,unsigned>> DF_number;
        
        // std::map<unsigned, std::set<CFGBlock *>> AV;
        
        for (auto *block : *(analDeclCtx.getCFG())){
            DF[block->getBlockID()]=std::set<unsigned>();
            DF2[block->getBlockID()]=std::set<unsigned>();
            DF1[block]=std::set<CFGBlock *>();
        }
        for (auto *block : *(analDeclCtx.getCFG())){
            if(block->pred_size()>=2)
            {
                for (CFGBlock::const_pred_iterator I = block->pred_begin(),
                     F = block->pred_end(); I != F; ++I)
                {
                    CFGBlock *runner=(*I);
                    CFGBlock *b;
                    while((b=domTree.DT->getNode(block)->getIDom()->getBlock()) && b->getBlockID()!=runner->getBlockID())
                    {
                        DF[runner->getBlockID()].insert(block->getBlockID());
                        runner=domTree.DT->getNode(runner)->getIDom()->getBlock();
                    }
                }
            }
        }
        
        /*   cytron/et al paper
         for each X in a bottom-up traversal of the dominator tree do
         >  DF(X) = empty
         >  for each Y in Successors(X)
         >    if (idom(Y) != X) then DF(X) += Y
         >  for each Z in DomChildren(X)
         >   for each Y in DF(Z)
         >     if (idom(Y) != X then DF(X) += Y  */
        
        DomTreeNode *root=domTree.getRootNode();
        std::queue<DomTreeNode *> dq;
        dq.push(root);
        while(!dq.empty())
        {
            DomTreeNode *current=dq.front();
            dq.pop();
            CFGBlock *curr=current->getBlock();
            for (CFGBlock::const_succ_iterator I = curr->succ_begin(),
                 F = curr->succ_end(); I != F; ++I)
            {
                CFGBlock *b=domTree.DT->getNode(*I)->getIDom()->getBlock();
                if(b->getBlockID()!=curr->getBlockID()){
                    DF1[curr].insert((*I));
                    DF2[curr->getBlockID()].insert((*I)->getBlockID());
                }
            }
            for(auto z:current->getChildren())
            {
                for(auto y:DF1[z->getBlock()])
                {
                    CFGBlock *idom=domTree.DT->getNode(y)->getIDom()->getBlock();
                    if(idom->getBlockID()!=curr->getBlockID()){
                        DF1[curr].insert(y);
                        DF2[curr->getBlockID()].insert(y->getBlockID());
                    }
                    
                }
                dq.push(z);
            }
            
        }
        
        unsigned iterCount=0;
        std::map<unsigned,unsigned> hasAlready, work;
        for (auto *block : *(analDeclCtx.getCFG())){
            hasAlready[block->getBlockID()]=0;
            work[block->getBlockID()]=0;
            
        }
        
        for (auto *block : *(analDeclCtx.getCFG())){
            if(block->pred_size()>1)
            {
                for(auto v:cfgAnal->getVars())
                    DF_number[block->getBlockID()][v]=0;
            }
        }
        
        std::queue<unsigned> W;
        for(auto v:cfgAnal->getVars())
        {
            iterCount = iterCount+1;
            std::set<CFGBlock *> bList=cfgAnal->getDefsOfVar(v);
            for(auto *block: bList)
            {
                work[block->getBlockID()]=iterCount;
                W.push(block->getBlockID());
            }
            while(!W.empty())
            {
                unsigned x=W.front();
                W.pop();
                for(auto y:DF2[x])
                {
                    if(hasAlready[y]<iterCount)
                    {
                        //llvm::errs()<<"\n"<<y<<" requires phi for "<<cfgAnal->getVarName(v);
                        DF_number[y][v]++;
                        hasAlready[y]=iterCount;
                        if(work[y]<iterCount)
                        {
                            work[y]=iterCount;
                            W.push(y);
                        }
                    }
                }
            }
        }
        
        if(_dl>2)
        for (auto *block : *(analDeclCtx.getCFG())){
            if(block->pred_size()>1)
            {
                for(auto v:cfgAnal->getVars())
                    if(DF_number[block->getBlockID()][v]>1)
                         llvm::errs()<<"\n"<<block->getBlockID()<<" requires phi for "<<cfgAnal->getVarName(v);
            }
        }
        
    }

    
    bool VisitFunctionDecl(FunctionDecl *f) {
        // Only function definitions (with bodies), not declarations.
         std::map<unsigned,std::set<unsigned> > phiNodesDF,pNodes;
        clang::SourceManager &sm(context.getSourceManager());
        if(!sm.isInMainFile(sm.getExpansionLoc(f->getBeginLoc())))
            return true;
        
        if (f->hasBody()) {
            
            Stmt *funcBody = f->getBody();
            std::unique_ptr<CFG> sourceCFG = CFG::buildCFG(f, funcBody, &context, CFG::BuildOptions());
            llvm::errs()<<"\n*****************************************************************\n";
            llvm::errs()<<"Analyzing CFG for function :"<<f->getNameInfo().getAsString()<<"\n";
            llvm::errs()<<"\nNo of CFG Nodes: "<<sourceCFG->size()<<"\n";
            //sourceCFG->dump(LangOptions(), true);
            /*if(!(f->getNameInfo().getAsString()=="Perl_scan_version2")) return false;
              sourceCFG->viewCFG(LangOptions());*/
            
            ClockTime start_time = Clock::now();
            CFGAnalysis *cfgAnal=new CFGAnalysis(std::move(sourceCFG),context,_dl);
            
           // ClockTime start_time2 = Clock::now();
            cfgAnal->dataflow_analysis();
            ClockTime end_time = Clock::now();
            printExecutionTime(start_time, end_time);
         
            cfgAnal->exportPhiResults(phiNodesDF);
            
            //Cytron's Method
            //printExecutionTime(start_time2, end_time);
            std::unique_ptr<CFG> cfg = CFG::buildCFG(f, funcBody, &context, CFG::BuildOptions());
            start_time = Clock::now();
            CFGAnalysis *cfg_analDF=new CFGAnalysis(std::move(cfg),context,_dl);
            computePhifunctions(f,cfg_analDF,pNodes);
            end_time = Clock::now();
            printExecutionTime(start_time, end_time);
            compare_results(f,cfg_analDF,phiNodesDF,pNodes);
            llvm::errs()<<"*****************************************************************\n";
        }
        return true;
    }
    /*
    void blockIdMap(const std::unique_ptr<CFG> &cfg)
    {
     for (auto *B : *cfg)
        idToBlock[B->getBlockID()]=B;
    }
    */
    
private:
    ASTContext &context;
    std::map<unsigned, CFGBlock*> idToBlock;
    unsigned _dl;
};


class CFGAstConsumer : public ASTConsumer {
public:
    CFGAstConsumer(ASTContext &C,unsigned dl) : Visitor(C,dl) {}
    
    // Override the method that gets called for each parsed top-level
    // declaration.
    bool HandleTopLevelDecl(DeclGroupRef DR) override {
        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
            // Traverse the declaration using our AST visitor.
            Visitor.TraverseDecl(*b);
            //(*b)->dump();
        }
        return true;
    }
    
private:
    CFGVisitor Visitor;
};


class CFGFrontendAction : public ASTFrontendAction {
    unsigned _dl;
 public:
    CFGFrontendAction(unsigned dl) {_dl=dl;}
    
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) {
        //TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
        return llvm::make_unique<CFGAstConsumer>(CI.getASTContext(),_dl);
    }
};

class CFGFrontendActionFactory : public clang::tooling::FrontendActionFactory {
    unsigned _dl;
public:
    CFGFrontendActionFactory (unsigned dl)
    : _dl (dl) { }
    
    virtual clang::FrontendAction *create () {
        return new CFGFrontendAction(_dl);
    }
};


int main(int argc,  const char **argv) {
    CommonOptionsParser op(argc, argv, MainCat);
    unsigned debugL=0;
    if(DL==O1) debugL=1;
    else if(DL==O2) debugL=2;
    else if(DL==O3) debugL=3;
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());
    CFGFrontendActionFactory cfgFact(debugL);
    //int result = Tool.run(newFrontendActionFactory<CFGFrontendAction>(debugL).get());
    int result = Tool.run(&cfgFact);
    return result;
}

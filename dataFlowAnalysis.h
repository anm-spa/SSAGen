//
//  dataFlowAnalysisg.h
//  LLVM
//
//  Created by Abu Naser Masud on 2019-02-22.
//

#ifndef dataFlowAnalysis_h
#define dataFlowAnalysis_h
//
//  dataflow_analysis.h
//  LLVM
//
//  Created by Abu Naser Masud on 2019-02-19.
//
#include <algorithm>
#include <vector>
#include <iterator>
using namespace llvm;
using namespace clang;

typedef std::pair< const CFGBlock *,const CFGBlock *> WElemT;

class VarInfoT{
    std::map<unsigned, std::string> VarMap;
    std::map<std::string,unsigned>  MapVar;
    unsigned id;
public:
    VarInfoT(){id=0;VarMap.clear(); MapVar.clear();}
    unsigned mapsto(std::string var)
    {
        auto it=MapVar.find(var);
        if(it!= MapVar.end())
            return it->second;
        else{
            VarMap[id]=var;
            MapVar[var]=id++;
            return id-1;
        }
    }
    std::string mapsfrom(unsigned varNum)
    {
        auto it=VarMap.find(varNum);
        if(it!= VarMap.end())
            return it->second;
        else{
            return "unknown variable";
        }
    }
};

class VarInfoInBlock
{
public:   // privacy should be changed
    std::vector<std::set<unsigned> > Defs;   //defs of each stmt
    std::vector<std::set<unsigned> > Refs;   // refs of each stmt
    std::set<unsigned> BlockDefs, BlockRefs;
    void insertVarInfo(std::set<unsigned> &D, std::set<unsigned> &R)
    {
        Defs.push_back(D);
        Refs.push_back(R);
        BlockDefs.insert(D.begin(),D.end());
        BlockRefs.insert(R.begin(),R.end());
    }
    bool isDef(unsigned v)
    {
        auto it=BlockDefs.find(v);
        if(it==BlockDefs.end()) return false;
        return true;
    }
};


class WorkListT
{
    std::map<unsigned,std::map<unsigned,unsigned> > edgeMap;
    std::queue<WElemT> WList;
    llvm::BitVector enqueuedEdge;
    llvm::BitVector visitedEdge;
    unsigned maxID;
public:
    WorkListT(){}
    WorkListT(WorkListT &w){
        edgeMap=w.getEdgeMap();
        maxID=w.getMaxID();
        enqueuedEdge=llvm::BitVector(maxID);
        visitedEdge=llvm::BitVector(maxID);
    }
    unsigned getMaxID(){ return maxID; }

    std::queue<WElemT> getWList()
    {
        return WList;
    }
    
    llvm::BitVector getenqueuedEdge(){
        return enqueuedEdge;
    }
    
    void copy(WorkListT *w)
    {
        WList=w->getWList();
        enqueuedEdge=w->getenqueuedEdge();
    }
    void clear()
    {
        while(!WList.empty())
            WList.pop();
        enqueuedEdge=llvm::BitVector(maxID);
    }
    
    void hasVisited(unsigned src, unsigned dest)
    {
       visitedEdge[edgeMap[src][dest]]=true;
    }
    
    bool isVisited(unsigned src, unsigned dest)
    {
      return visitedEdge[edgeMap[src][dest]];
    }
    bool allPredVisited(const CFGBlock* blk)
    {
        bool status=true;
        for(auto b:blk->preds())
        {
            if(!b.isReachable()) continue;
            status=status & visitedEdge[edgeMap[(*b).getBlockID()][blk->getBlockID()]];
        }
        return status;
    }
    
    std::map<unsigned,std::map<unsigned,unsigned> > getEdgeMap(){ return edgeMap; }
    
    void initializeEdgeMap(std::unique_ptr<CFG> &cfg,std::map<unsigned,unsigned> &nEdge)
    {
        unsigned eID=0;
        SmallVector<const CFGBlock *, 20> W;
        llvm::BitVector visited(cfg->getNumBlockIDs());
        W.push_back(&cfg->getEntry());
        while(!W.empty())
        {
            const CFGBlock *B=W.pop_back_val();
            visited[B->getBlockID()] = true;
            std::map<unsigned,unsigned> val;
            for (CFGBlock::const_succ_iterator I = B->succ_begin(),
                 E = B->succ_end(); I != E; ++I) {
                if(!(*I)) continue; // check for unreachable block
               // llvm::errs()<<B->getBlockID()<<"->"<<(*I)->getBlockID()<<"\n";
                val.insert(std::make_pair((*I)->getBlockID(),eID++));
                nEdge[eID-1]=0;
                if(!visited[(*I)->getBlockID()])
                    W.push_back(*I);
            }
            edgeMap[B->getBlockID()]=val;
        }
        enqueuedEdge=llvm::BitVector(eID);
        visitedEdge=llvm::BitVector(eID);
        maxID=eID;
    }
    
    void enqueue(const CFGBlock *Src, const CFGBlock *Dst) {
        unsigned eID=edgeMap[Src->getBlockID()][Dst->getBlockID()];
        if(!enqueuedEdge[eID]){
            WList.push(std::make_pair(Src,Dst));
            enqueuedEdge[eID]=true;
        }
    }

    WElemT dequeue() {
        if (WList.empty()) return WElemT();
        WElemT elem=WList.front();
        WList.pop();
        unsigned eID=edgeMap[elem.first->getBlockID()][elem.second->getBlockID()];
        enqueuedEdge[eID]=false;
        return elem;
    }
    
    bool notEmpty()
    {
        return !WList.empty();
    }
    unsigned edgeID(unsigned src, unsigned des)
    {
        return edgeMap[src][des];
    }
};


// AEntry, AExit maps from BlockID -> Var-> (DataVal, Status)

class DFAnalysis
{
    typedef std::set<unsigned> DataT;
    typedef std::map<unsigned,DataT> VarDataT;
    std::map<unsigned, VarDataT> AEntry, AExit;
    WorkListT workList;
    VarInfoT varInfo;
    std::map<unsigned, CFGBlock*> idToBlock;
    std::set<unsigned> inputVars;
    std::map<unsigned, std::map <unsigned,unsigned > > fmap;
    unsigned maxNode;
    unsigned EntryID;
    std::map<unsigned, std::map<unsigned,std::set<unsigned> > > jMap;
    struct CFGBlockInfo
    {
        std::set<unsigned> preds, succs;
    };
    
    std::map<unsigned, struct CFGBlockInfo> blockMap;
    std::map<unsigned,unsigned> muN, invMuN;
    unsigned debug_level;
    
public:
    std::map<unsigned,unsigned> numNodeVisit;
    std::map<unsigned,unsigned> numEdgeVisit;
    
    DFAnalysis(){}
    DFAnalysis(std::unique_ptr<CFG> &cfg,std::set<unsigned> vars, VarInfoT &vInfo, unsigned dl=0)
    {
       // llvm::errs()<<"Initializing DF analysis\n";
        maxNode=cfg->size();
        for (auto *block : *cfg)
        {
            VarDataT vDataEntry, vDataExit;
            for(auto v:vars)
            {
                vDataEntry.insert(std::make_pair(v,std::set<unsigned>()));
                vDataExit.insert(std::make_pair(v,std::set<unsigned>()));
                fmap[block->getBlockID()][v]=block->getBlockID();
            }
            AEntry.insert(std::make_pair(block->getBlockID(),vDataEntry));
            AExit.insert(std::make_pair(block->getBlockID(),vDataExit));
            numNodeVisit[block->getBlockID()]=0;        // for collecting statistics
            
            // muN is an id-function for all valid CFG nodes, but returns the originating node of unknown definition. invMuN is the inverse function of muN of all valid node
            muN[block->getBlockID()]=block->getBlockID();
            muN[maxNode+block->getBlockID()]=block->getBlockID();
            invMuN[block->getBlockID()]=maxNode+block->getBlockID();
            
            // initialization of predecessor and sucessors of CFGBlock
            CFGBlockInfo cblock;
            cblock.preds=std::set<unsigned>();
            cblock.succs=std::set<unsigned>();
            blockMap[block->getBlockID()]=cblock;
            idToBlock[block->getBlockID()]=block;
        }
        CFGBlock &entry=cfg->getEntry();
        EntryID=entry.getBlockID();
        visitReachableBlocks(&entry);   // Refine CFG succs and preds
        
        workList.initializeEdgeMap(cfg,numEdgeVisit);
        
        for(CFGBlock::const_succ_iterator I = entry.succ_begin(),
            E = entry.succ_end(); I != E; ++I) {
            workList.enqueue(&entry,*I);
        }
        varInfo=vInfo;
        debug_level=dl;
       // Debug information of CFG generated by Clang
       /*
       for (auto *B : *cfg) {
           llvm::errs()<<"Block: "<<B->getBlockID()<<"# succs: ";
           for(auto b:blockMap[B->getBlockID()].succs)
               llvm::errs()<<b<<", ";
           llvm::errs()<<"Preds ";
           for(auto b:blockMap[B->getBlockID()].preds)
               llvm::errs()<<b<<", ";
           llvm::errs()<<"\n";
       }*/
    }
    
    /* This is an utility function. Clang generates CFG which contains null node pointer that is reachable and creates segmentation fault during CFG traversal.
       This function helps refining the CFG and remove all null nodes.
    */
    
    void visitReachableBlocks(clang::CFGBlock *B)
    {
       std::queue<clang::CFGBlock*> wList;
       llvm::BitVector visited(maxNode);
        wList.push(B);
        while (!wList.empty()) {
            CFGBlock* bl=wList.front();
            wList.pop();
            visited[bl->getBlockID()]=true;
            for (CFGBlock::const_succ_iterator I = bl->succ_begin(),
                 F = bl->succ_end(); I != F; ++I)
            {
                if(!(*I)) continue;
               // llvm::errs()<<"Considering edge "<<bl->getBlockID()<<" to "<<(*I)->getBlockID()<<"\n";
                blockMap[bl->getBlockID()].succs.insert((*I)->getBlockID());
                blockMap[(*I)->getBlockID()].preds.insert(bl->getBlockID());
                if(!visited[(*I)->getBlockID()])  wList.push(*I);
            }
        }
    }
    
    // Printing internal steps of the analysis
    void print_nodeInfo(unsigned n,unsigned v)
    {
        if(debug_level<2) return;
        llvm::errs()<<"info("<<n<<", "<<*(AExit[n][v].begin())<<") = ";
        for(auto d: AEntry[n][v])
            llvm::errs()<<d<<" ";
        llvm::errs()<<"\n";
    }
    
    void printPhiNodes(std::unique_ptr<CFG> &cfg,std::set<unsigned> vars)
    {
        for (auto *block : *cfg){
            unsigned bID=block->getBlockID();
            if(block->pred_size()>1)
            {
                for(auto v:vars)
                {
                    if(AEntry[bID][v].size()>1)
                        llvm::errs()<<"Block "<<bID<<" requires phi function for variable "<<varInfo.mapsfrom(v)<<"\n";
                }
            }
        }
    }
    
    void debug_print(unsigned id,std::set<unsigned> &vars)
    {
        if(debug_level<2) return;
        llvm::errs()<< "AEntry B"<<id<<"\n";
        for(auto v:vars)
            //for(auto v:inputVars)
        {
            std::string vn=varInfo.mapsfrom(v);
            if(AEntry[id][v].empty())
                llvm::errs()<< "Var "<<vn<<": [], ";
            else
            {   llvm::errs()<< "Var "<<vn<<": ";
                for(auto I=AEntry[id][v].begin(), F=AEntry[id][v].end();I!=F;I++)
                    llvm::errs()<<*I<<" ";
            }
            llvm::errs()<<" \n";
        }
        llvm::errs()<< "AExit: "<<id<<"\n";
        for(auto v:vars)
            //for(auto v:inputVars)
        {
            std::string vn=varInfo.mapsfrom(v);
            if(AExit[id][v].empty())
                llvm::errs()<< "Var "<<vn<<": [], ";
            else
            {   llvm::errs()<< "Var "<<vn<<": ";
                for(auto I=AExit[id][v].begin(), F=AExit[id][v].end();I!=F;I++)
                    llvm::errs()<<*I<<" ";
            }
            llvm::errs()<<" \n\n";
        }
    }
    
    void printDFValues_withDebug(std::unique_ptr<CFG> &cfg,std::set<unsigned> vars,std::map<unsigned,VarInfoInBlock> &blockToVars)
    {
        
        std::set<unsigned, std::greater<unsigned>> jNodes,joinNodes;
        for(auto v:vars){
            llvm::errs()<<"\nTable of "<<v<<"\n";
            for (auto *block : *cfg){
                unsigned bID=block->getBlockID();
                jMap[bID][v]=std::set<unsigned>();
                jNodes.insert(bID);
                if(blockMap[bID].preds.size()>1)
                {
                    joinNodes.insert(bID);
                    unsigned k=*(AExit[bID][v].begin());
                    llvm::errs()<<"Value ("<<bID<<", "<<k<<") = ";
                    for(auto d: AEntry[bID][v])
                    {
                        llvm::errs()<<d<<" ";
                        jMap[bID][v].insert(d);
                    }
                    llvm::errs()<<"\n";
                }
                else {
                    unsigned k=*(AExit[bID][v].begin());
                    llvm::errs()<<"Value ("<<bID<<", "<<k<<") = ";
                    for(auto d: AEntry[bID][v])
                    {
                        llvm::errs()<<d<<" ";
                        jMap[bID][v].insert(d);
                    }
                    llvm::errs()<<"\n";
                }
            }
            resolve_equations(jNodes,joinNodes,v,blockToVars);
        }
    }
    
    void printDFValues(std::unique_ptr<CFG> &cfg,std::set<unsigned> vars,std::map<unsigned,VarInfoInBlock> &blockToVars)
    {
        
        std::set<unsigned, std::greater<unsigned>> jNodes,joinNodes;
        for(auto v:vars){
           for (auto *block : *cfg)
           {
              unsigned bID=block->getBlockID();
              jMap[bID][v]=std::set<unsigned>();
              jNodes.insert(bID);
              jMap[bID][v].insert(AEntry[bID][v].begin(),AEntry[bID][v].end());
              if(blockMap[bID].preds.size()>1)
                  joinNodes.insert(bID);
              
            }
            resolve_equations(jNodes,joinNodes,v,blockToVars);
      }
   }
    
    unsigned forward_resolution(std::set<unsigned> R,unsigned d,unsigned v)
    {
        std::set<unsigned> R1,R2;
        R1.insert(R.begin(),R.end());
        R2.insert(R.begin(),R.end());
        for(auto n:jMap[muN[d]][v])
        {
            if(n>=maxNode) R1.insert(muN[d]);
            else R2.insert(n);
        }
        
        if(R1.size()>=2 && R2.size()>=2) return 2;
        if(R2.size()>=2 && R1.size()==0) return 2;
        return 0;
    }
    
    unsigned calculateMu(unsigned n,unsigned D, unsigned v, std::set<unsigned> S, std::map<unsigned,VarInfoInBlock> &blockToVars,llvm::BitVector &inProcessing, llvm::BitVector &Visit)
    {
        std::set<unsigned> R={},NotResolved={};
        llvm::BitVector V(2*maxNode);
        if(inProcessing[D]) return D;
    
        while((S.size()==1) && *S.begin()>=maxNode && !inProcessing[*S.begin()]) {
            unsigned val=*S.begin();
            std::set<unsigned> S1=jMap[muN[val]][v];
            if(!(blockToVars[n].isDef(v)))
              S1.erase(D);
            if(S1.size()>1) break;
            S=S1;
            jMap[n][v]=S1;
        } 
            
        for(auto d:S)
        {
            if(V[d]) continue;
            if((*AExit[n][v].begin()==d) && !(blockToVars[n].isDef(v)) && jMap[muN[d]][v].size()>1) continue;
            std::set<unsigned> s=std::set<unsigned>();
            s.insert(d);
            if((jMap[muN[d]][v]==s)  || (d<maxNode) )
            {
                R.insert(d);
                if(R.size()>1)
                {
                  jMap[n][v]={n};
                  AExit[n][v]={n};
                }
            }
            else if(d==D || d==n)
            {
                V[d]=true;
                continue;
            }
            else if(inProcessing[d])
                NotResolved.insert(d);
            
            else if(Visit[muN[d]])
            {
                R.insert(*AExit[muN[d]][v].begin());
                if(R.size()>1)
                {
                    jMap[n][v]={n};
                    AExit[n][v]={n};
                }
            }
            else{
                if(R.size()<= 1)
                if(forward_resolution(R,d,v))
                {
                    jMap[n][v]={n};
                    AExit[n][v]={n};
                }
               // inProcessing.insert(invMuN[n]);   // or invMun?
                inProcessing[invMuN[n]]=true;
                unsigned k=calculateMu (muN[d],d,v,jMap[muN[d]][v],blockToVars,inProcessing,Visit);
                 inProcessing[invMuN[n]]=false;
                if(k>=maxNode) {
                    if(forward_resolution(R,k,v))
                    {
                        jMap[n][v]={n};
                        AExit[n][v]={n};
                        R.insert(muN[k]);
                    }
                    else if(k!=D) NotResolved.insert(k);
                }
                else R.insert(k);
            }
            V[d]=true;
        }
            if(R.size()>1)
            {
                jMap[n][v]={n};
                AEntry[n][v]=R;
                AExit[n][v]={n};
                Visit[n]=true;
                return n;
            }
            else if(R.size()<=1 && NotResolved.empty()){
              jMap[n][v]={*R.begin()};
              AEntry[n][v]=R;
              AExit[n][v]=R;
              Visit[n]=true;
              return *R.begin();
            }
           else if(mutual_resolution(R,n,NotResolved,v))
           {
               jMap[n][v]={n};
               AExit[n][v]={n};
               return n;
           }
            else // if(!NotResolved.empty())
            {
              std::set<unsigned> T={};
              T.insert(R.begin(),R.end());
              T.insert(NotResolved.begin(),NotResolved.end());
             // T.erase(D);
              jMap[n][v]=T;
              if(T.size()< 2) return *T.begin();
              return D;
            }
    }
    
    bool mutual_resolution(std::set<unsigned> R, unsigned D, std::set<unsigned> Nr,unsigned v)   // extend this function
    {
        R.insert(D);
        for(auto n:Nr)
        {
            std::set<unsigned> RR,diff;
            for(auto d:jMap[n][v])
                if(d<maxNode) RR.insert(d);
                //else RR.insert(muN[n]);
            if(RR.size()>0) RR.insert(muN[n]);
            std::set_intersection (R.begin(), R.end(),RR.begin(), RR.end(),
                 std::inserter(diff, diff.begin()));
            
            if(diff.empty() && R.size()>1 && RR.size()>1)
                return true;
        }
        return false;
    }
    
    
    
    
    void cyclic_resolution_aux(unsigned n, unsigned v, std::map<unsigned, std::set<unsigned>> &parentOf,std::set<unsigned> &resolved, llvm::BitVector &V)
    {
        V[n]=true;
        for(auto d:jMap[muN[n]][v])
        {
          if(!V[d]){
              parentOf[d]={n};
              if(d<maxNode) resolved.insert(d);
              else cyclic_resolution_aux(d,v,parentOf,resolved,V);
            }
            else{
                parentOf[d].insert(n);
               }
        }
    }
    
    void cyclic_assignment(std::set<unsigned> res,std::map<unsigned, std::set<unsigned> > parentOf, std::map<unsigned, std::set<unsigned> > &resolved, std::set<unsigned> &nonResolved)
    {
        for(auto m:res)
        {   unsigned M=2*maxNode+1;
            std::vector<unsigned> W;
            llvm::BitVector V(2*maxNode+2);
            V[M]=true;
            for(auto d:parentOf[m])
               W.push_back(d);
            while(W.size()>0)
            {
                unsigned q=W.back();
                W.pop_back();
                if(q==M) continue;
                nonResolved.insert(q);
                resolved[q].insert(m);
                V[q]=true;
                for(auto d:parentOf[q])
                    if(!V[d])
                        W.push_back(d);
            }
        }
    }
    unsigned cyclic_resolution(unsigned D, unsigned v, llvm::BitVector &Visit)
    {
        std::set<unsigned> nonResolved={},res={};
        std::map<unsigned, std::set<unsigned> > parentOf,resolved;
        
        llvm::BitVector V(2*maxNode);
     
        parentOf[D]={2*maxNode+1};
        //cyclic_resolution_aux(D,v,paren, resolved,nonResolved,V);
        cyclic_resolution_aux(D,v, parentOf,res,V);
        cyclic_assignment(res,parentOf, resolved, nonResolved);
        for(auto m:nonResolved)
        {
           if(resolved[m].size()>1)
           {
               std::set<unsigned> S;
              // for(auto d:jMap[muN[m]][v])
                //   S.insert(muN[d]);
               jMap[muN[m]][v]={muN[m]};
               AEntry[muN[m]][v]=resolved[m];   // resolved[m] or S
               AExit[muN[m]][v]={muN[m]};
               Visit[muN[m]]=true;
           }
            else if(resolved[m].size()==1)
            {
                unsigned p=muN[m];
                jMap[p][v]=resolved[m];
                AEntry[p][v]=resolved[m];
                AExit[p][v]=resolved[m];
                Visit[p]=true;
            }
        }
        if(resolved[D].size()>1) {resolved.clear(); return muN[D];}
        else if(resolved[D].size()==1) {resolved.clear(); return *resolved[D].begin();}
        resolved.clear();
        return D;
    }
    
    
    void exportResults(std::unique_ptr<CFG> &cfg,std::set<unsigned> vars, std::map<unsigned,std::set<unsigned> > &phiNodes)
    {
        for (auto *block : *cfg){
            unsigned bID=block->getBlockID();
            phiNodes[bID]=std::set<unsigned>();
            if(block->pred_size()>1)
            {
                for(auto v:vars)
                {
                    if(AEntry[bID][v].size()>1)
                        phiNodes[bID].insert(v);
                       //llvm::errs()<<"Block "<<bID<<" requires phi function for variable "<<varInfo.mapsfrom(v)<<"\n";
                }
            }
        }
        
    }
    
    unsigned edgeID(unsigned src,unsigned des)
    {
        return workList.edgeID(src,des);
    }
    
    bool lessThanQual(DataT oldV,DataT newV,int k)
    {
        if(!(oldV==newV)) return true;
     //   if(!(oldV.second==newV.second)) return true;
        if(oldV.empty() && !k) return true;
        return false;
    }
    
    bool lessThanQualSet(std::set<unsigned> oldV, std::set<unsigned> newV,int k)
    {

        if(!(oldV==newV)) return true;
        if(oldV.empty() && !k) return true;
        return false;
    }
    
    bool lessThanQualVal(DataT oldV,DataT newV)
    {
        if(!(oldV==newV)) return true;
        if(oldV.empty()) return true;
        return false;
    }
    
    
    void resolve_equations(std::set<unsigned, std::greater<unsigned>> jNodes, std::set<unsigned, std::greater<unsigned>> joinNodes,unsigned v,std::map<unsigned,VarInfoInBlock> &blockToVars)
    {
        unsigned counter=0;
        llvm::BitVector V(maxNode);
        do{
            counter++;
            std::set<unsigned, std::greater<unsigned>> unresolvedNodes={};
            for(auto n:joinNodes)
            {
                // std::set<unsigned> Sp;
                llvm::BitVector inProcessing(2*maxNode);
                if(V[n]) continue;
                unsigned k=calculateMu (n,*(AExit[n][v].begin()),v,jMap[n][v],blockToVars,inProcessing,V);
                if(k==*(AExit[n][v].begin()) && k>=maxNode) k= cyclic_resolution(k,v,V);
                if(k >=maxNode) unresolvedNodes.insert(n);
            }
            if(unresolvedNodes.empty()) break;
            joinNodes=unresolvedNodes;
            if(counter>10) {
                llvm::errs()<<"Possibly an infinite loop: ";
                for(auto d:unresolvedNodes)
                    llvm::errs()<<d<<" ";
                llvm::errs()<<"\n";
                break;
            }
        }while(true);
        
        /*
        for(auto n:joinNodes)
        {
            llvm::errs()<<"Value ("<<n<<", "<<*(AExit[n][v].begin())<<") = ";
            for(auto d: AEntry[n][v])
                llvm::errs()<<d<<" ";
            llvm::errs()<<"\n";
        }
        llvm::errs()<<"\n";
        */
    }
    
    
    // Main Fixpoint computation
    void computeFixpoint(std::set<unsigned> &vars, std::map<unsigned,VarInfoInBlock> &blockToVars)
    {
        WorkListT *wList1;
        wList1 =&workList;
        llvm::BitVector processed(maxNode);
        
        while (wList1->notEmpty()) {
            
            llvm::BitVector visited(workList.getMaxID());
            std::set<unsigned> toBeProcessed;
            while(wList1->notEmpty()){
                 WElemT E=wList1->dequeue();
                 if(debug_level>1)
                 llvm::errs()<<"Fixpoint iteration:"<<E.first->getBlockID()<<"->"<<E.second->getBlockID()<< "\n";
                 applyTF(E.first,vars,blockToVars);
                
                 debug_print(E.first->getBlockID(),vars);
                
                 numEdgeVisit[workList.edgeID(E.first->getBlockID(),E.second->getBlockID())]++;
                 numNodeVisit[E.first->getBlockID()]++;
                 workList.hasVisited(E.first->getBlockID(),E.second->getBlockID());
                 visited[workList.edgeID(E.first->getBlockID(),E.second->getBlockID())]=true;
                 bool status=workList.allPredVisited(E.second);
                // processed[E.first->getBlockID()]=true;
                 for(auto v:vars)
                 {
                    std::set<unsigned> defs;
                    for(auto pre_B:blockMap[E.second->getBlockID()].preds)
                    {
                        if(!AExit[pre_B][v].empty() && workList.isVisited(pre_B, E.second->getBlockID()))
                        {
                            unsigned i=*(AExit[pre_B][v].begin());
                            defs.insert(i);
                        }
                        else defs.insert(invMuN[pre_B]);
                    }
                    if(lessThanQualVal(AEntry[E.second->getBlockID()][v],defs))
                    {
                        AEntry[E.second->getBlockID()][v]=defs;
                        if(status){
                           for (CFGBlock::const_succ_iterator I = E.second->succ_begin(),
                                F = E.second->succ_end(); I != F; ++I)
                            {
                              if(!(*I)) continue; // ignore unreachable block
                              if(!visited[workList.edgeID(E.second->getBlockID(),(*I)->getBlockID())])
                                  wList1->enqueue(E.second,*I);
                            }
                            processed[E.second->getBlockID()]=false;
                        }
                        else{
                             processed[E.second->getBlockID()]=true; //wList2->enqueue(E.second,*I);
                             toBeProcessed.insert(E.second->getBlockID());
                        }
                    }
                }
                
                // llvm::errs()<<"Update AExit "<<E.second->getBlockID()<<"\n";
                //  debug_print(E.second->getBlockID(),vars);
            }
            for(auto b:toBeProcessed)
            {
                if(processed[b]){
                    for (auto d:blockMap[b].succs)
                        if(!visited[workList.edgeID(b,d)])
                          wList1->enqueue(idToBlock[b],idToBlock[d]);
                   // llvm::errs()<<b<<" ";
                    processed[b]=false;
                }
                //llvm::errs()<<"\n";
            }
        }
    }
    
    
    void applyTF(const CFGBlock *cfgblock, std::set<unsigned> &vars, std::map<unsigned,VarInfoInBlock> &blockToVars)
    {
        unsigned bID=cfgblock->getBlockID();
        if(blockMap[bID].preds.size() <=1)
        {
            for(auto v:vars)
            {
                if(blockToVars[bID].isDef(v))
                {
                    std::set<unsigned> s={bID};
                    AExit[bID][v]=s;
                }
                else  AExit[bID][v]=AEntry[bID][v];
            }
        }
        else{     // It is a join node
            for(auto v:vars)
            {
                unsigned size=AEntry[bID][v].size();
                std::set<unsigned> s;
                bool status=true;
                for(auto d:AEntry[bID][v])
                {
                    if(d==maxNode+bID) size=size-1;
                    else if(muN[d]!=d) status=false;
                }
                if(blockToVars[bID].isDef(v))
                {
                    s={bID};
                    AExit[bID][v]=s;
                }
                else if(status && size>1){
                    s={bID};
                    AExit[bID][v]=s;
                }
                else if(!status)
                {
                    s={invMuN[bID]};
                    AExit[bID][v]=s;
                }
                
                else
                {
                    AExit[bID][v]=AEntry[bID][v];
                }
            }
        }
        return;
    }
};


#endif /* dataFlowAnalysis_h */

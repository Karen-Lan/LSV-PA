#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"
#include "aig/aig/aig.h"
#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_map> 
using namespace std;

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPOunate(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintPounate(Abc_Frame_t *pAbc, int argc, char **argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd( pAbc, "LSV", "lsv_print_sopunate", Lsv_PrintSopunate_Command, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_pounate", Lsv_CommandPrintPounate, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData); //Abc_ObjData( Abc_Obj_t * pObj )
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int j;
  Extra_UtilGetoptReset();
  while ((j = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (j) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

//=======================
//Print_Sopunate_Command
//=======================
void print_unateness(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate);
bool object_id_compare (Abc_Obj_t* a, Abc_Obj_t* b) { return (Abc_ObjId(a) < Abc_ObjId(b)); }
int Lsv_PrintSopunate_Command(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  Abc_Obj_t* pObj;
  Abc_Obj_t* pFanin;
  char * pSop, * pCube;
  int nVars, Value;
  int i, j, k; //i: each node, j: cube for each var, k: each fanin
  int *A;

  vector<Abc_Obj_t*> pos_unate, neg_unate, binate;

  Abc_NtkForEachNode(pNtk, pObj, i) {
    if(Abc_ObjFaninNum(pObj) == 0) continue;

    printf("node %s:\n", Abc_ObjName(pObj));

    if(Abc_NtkHasSop(pNtk)) { 
      pSop = (char*)Abc_ObjData(pObj);
      //printf("The SOP of this node:\n%s", pSop);

      nVars = Abc_SopGetVarNum(pSop);
      //new array
      A = new int[nVars];
      for(int m = 0; m < nVars; m++) //initialization
        A[m] = -1;

      Abc_SopForEachCube( pSop, nVars, pCube ) {
        Abc_CubeForEachVar( pCube, Value, j ) {
          //printf("Value=%d, A[%d]=%d\n", Value, j, A[j]);
          if(A[j] == -1) {
            if(Value == '0' || Value == '1') {
              A[j] = Value - '0';
            }
          }
          else if((A[j]==1 && Value=='0') || (A[j]==0 && Value=='1'))
            A[j] = 3; //binate     
        }
      }

      //catagorize
      Abc_ObjForEachFanin(pObj, pFanin, k) {
        if(A[k] == 1)
          pos_unate.push_back(pFanin);
        else if(A[k] == 0)
          neg_unate.push_back(pFanin);
        else if(A[k] == 3) {
          binate.push_back(pFanin);
          
        }else if(A[k] == -1) {
          pos_unate.push_back(pFanin);
          neg_unate.push_back(pFanin);
        }
      }
      
      delete[] A;

      // sort by object id
      sort(pos_unate.begin(), pos_unate.end(), object_id_compare);
      sort(neg_unate.begin(), neg_unate.end(), object_id_compare);
      sort(binate.begin(), binate.end(), object_id_compare);

      //print
      if(Abc_SopGetPhase(pSop) == 1) 
        print_unateness(pos_unate, neg_unate, binate);
      else 
        print_unateness(neg_unate, pos_unate, binate); // Abc_SopGetPhase(pSop) == 0 --> negate
    

      pos_unate.clear();
      neg_unate.clear();
      binate.clear();

    }
    
  }
  return 0;
}

void print_unateness(vector<Abc_Obj_t*> &pos_unate, vector<Abc_Obj_t*> &neg_unate, vector<Abc_Obj_t*> &binate) {
  if(pos_unate.size() != 0){
    printf("+unate inputs: ");
    for(int m = 0; m < pos_unate.size(); m++) {
      if(m == pos_unate.size() - 1)
        printf("%s\n", Abc_ObjName(pos_unate[m]));
      else  
        printf("%s,", Abc_ObjName(pos_unate[m]));
    }
  }
        
  if(neg_unate.size() != 0){
    printf("-unate inputs: ");
    for(int m = 0; m < neg_unate.size(); m++) {
      if(m == neg_unate.size() - 1)
        printf("%s\n", Abc_ObjName(neg_unate[m]));
      else  
        printf("%s,", Abc_ObjName(neg_unate[m]));
    }
  }

  if(binate.size() != 0){
    printf("binate inputs: ");
    for(int m = 0; m < binate.size(); m++) {
      if(m == binate.size() - 1)
        printf("%s\n", Abc_ObjName(binate[m]));
      else  
        printf("%s,", Abc_ObjName(binate[m]));
    }
  }
}

/**Function*************************************************************

  Synopsis    [Converts the network from the AIG manager into ABC.]

  Description [Assumes that registers are ordered after PIs/POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters )
{
    Vec_Ptr_t * vNodes;
    Aig_Man_t * pMan;
    Aig_Obj_t * pObjNew;
    Abc_Obj_t * pObj;
    int i, nNodes, nDontCares;
    // make sure the latches follow PIs/POs
    if ( fRegisters ) 
    { 
        assert( Abc_NtkBoxNum(pNtk) == Abc_NtkLatchNum(pNtk) );
        Abc_NtkForEachCi( pNtk, pObj, i )
            if ( i < Abc_NtkPiNum(pNtk) )
            {
                assert( Abc_ObjIsPi(pObj) );
                if ( !Abc_ObjIsPi(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PI ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBo(pObj) );
        Abc_NtkForEachCo( pNtk, pObj, i )
            if ( i < Abc_NtkPoNum(pNtk) )
            {
                assert( Abc_ObjIsPo(pObj) );
                if ( !Abc_ObjIsPo(pObj) )
                    Abc_Print( 1, "Abc_NtkToDar(): Temporary bug: The PO ordering is wrong!\n" );
            }
            else
                assert( Abc_ObjIsBi(pObj) );
        // print warning about initial values
        nDontCares = 0;
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInitDc(pObj) )
            {
                Abc_LatchSetInit0(pObj);
                nDontCares++;
            }
        if ( nDontCares )
        {
            Abc_Print( 1, "Warning: %d registers in this network have don't-care init values.\n", nDontCares );
            Abc_Print( 1, "The don't-care are assumed to be 0. The result may not verify.\n" );
            Abc_Print( 1, "Use command \"print_latch\" to see the init values of registers.\n" );
            Abc_Print( 1, "Use command \"zero\" to convert or \"init\" to change the values.\n" );
        }
    }
    // create the manager
    pMan = Aig_ManStart( Abc_NtkNodeNum(pNtk) + 100 );
    pMan->fCatchExor = fExors;
    pMan->nConstrs = pNtk->nConstrs;
    pMan->nBarBufs = pNtk->nBarBufs;
    pMan->pName = Extra_UtilStrsav( pNtk->pName );
    pMan->pSpec = Extra_UtilStrsav( pNtk->pSpec );
    // transfer the pointers to the basic nodes
    Abc_AigConst1(pNtk)->pCopy = (Abc_Obj_t *)Aig_ManConst1(pMan);
    Abc_NtkForEachCi( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_ObjCreateCi(pMan);
        // initialize logic level of the CIs
        ((Aig_Obj_t *)pObj->pCopy)->Level = pObj->Level;
    }

    // complement the 1-values registers
    if ( fRegisters ) {
        Abc_NtkForEachLatch( pNtk, pObj, i )
            if ( Abc_LatchIsInit1(pObj) )
                Abc_ObjFanout0(pObj)->pCopy = Abc_ObjNot(Abc_ObjFanout0(pObj)->pCopy);
    }
    // perform the conversion of the internal nodes (assumes DFS ordering)
//    pMan->fAddStrash = 1;
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
//    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        pObj->pCopy = (Abc_Obj_t *)Aig_And( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj), (Aig_Obj_t *)Abc_ObjChild1Copy(pObj) );
//        Abc_Print( 1, "%d->%d ", pObj->Id, ((Aig_Obj_t *)pObj->pCopy)->Id );
    }
    Vec_PtrFree( vNodes );
    pMan->fAddStrash = 0;
    // create the POs
    Abc_NtkForEachCo( pNtk, pObj, i )
        Aig_ObjCreateCo( pMan, (Aig_Obj_t *)Abc_ObjChild0Copy(pObj) );
    // complement the 1-valued registers
    Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
    if ( fRegisters )
        Aig_ManForEachLiSeq( pMan, pObjNew, i )
            if ( Abc_LatchIsInit1(Abc_ObjFanout0(Abc_NtkCo(pNtk,i))) )
                pObjNew->pFanin0 = Aig_Not(pObjNew->pFanin0);
    // remove dangling nodes
    nNodes = (Abc_NtkGetChoiceNum(pNtk) == 0)? Aig_ManCleanup( pMan ) : 0;
    if ( !fExors && nNodes )
        Abc_Print( 1, "Abc_NtkToDar(): Unexpected %d dangling nodes when converting to AIG!\n", nNodes );
//Aig_ManDumpVerilog( pMan, "test.k" );
    // save the number of registers
    if ( fRegisters )
    {
        Aig_ManSetRegNum( pMan, Abc_NtkLatchNum(pNtk) );
        pMan->vFlopNums = Vec_IntStartNatural( pMan->nRegs );
//        pMan->vFlopNums = NULL;
//        pMan->vOnehots = Abc_NtkConverLatchNamesIntoNumbers( pNtk );
        if ( pNtk->vOnehots )
            pMan->vOnehots = (Vec_Ptr_t *)Vec_VecDupInt( (Vec_Vec_t *)pNtk->vOnehots );
    }
    if ( !Aig_ManCheck( pMan ) )
    {
        Abc_Print( 1, "Abc_NtkToDar: AIG check has failed.\n" );
        Aig_ManStop( pMan );
        return NULL;
    }
    return pMan;
}

void add_po_clauses(sat_solver * pSat, Cnf_Dat_t * pCnf, Cnf_Dat_t * pCnfdup) {
  int Lits[1], retval;
  assert(Aig_ManCoNum(pCnf->pMan) == 1);

  // f
  Lits[0] = toLitCond(pCnf->pVarNums[Aig_ObjId(Aig_ManCo(pCnf->pMan, 0))], 0);
  retval = sat_solver_addclause(pSat, Lits, Lits + 1);

  // negate f
  Lits[0] = toLitCond(pCnfdup->pVarNums[Aig_ObjId(Aig_ManCo(pCnf->pMan, 0))], 1);
  retval = sat_solver_addclause(pSat, Lits, Lits + 1);
}
void add_pi_clauses(sat_solver * pSat, Cnf_Dat_t * pCnf, Cnf_Dat_t * pCnfdup) {
    Aig_Obj_t *Aig_pObj;
    int i;

    sat_solver_setnvars(pSat, 2 * (pCnf->nVars) + Aig_ManCiNum(pCnf->pMan));
    Aig_ManForEachCi(pCnf->pMan, Aig_pObj, i) {

      int fvar = pCnf->pVarNums[Aig_ObjId(Aig_pObj)];
      int fneg_var = pCnfdup->pVarNums[Aig_ObjId(Aig_pObj)];
      int enable_var = 2 * (pCnf->nVars) + i;
      
      sat_solver_add_buffer_enable(pSat, fvar, fneg_var, enable_var, 0);
    }
}

int Lsv_CommandPrintPounate(Abc_Frame_t *pAbc, int argc, char **argv)
{
  Abc_Ntk_t *pNtk = Abc_FrameReadNtk(pAbc);

  Abc_Obj_t *pObjPO, *pObjPI;
  Aig_Obj_t *Aig_pObj;
  int i, j, k;

  Abc_Ntk_t *pNtkConed;
  Aig_Man_t *pMan;
  Cnf_Dat_t *pCnf, *pCnfdup;
  sat_solver * pSat;

  unordered_map<int, string> id2name;
  unordered_map<string, char> name2unate;
  vector<Abc_Obj_t *> pos_unate, neg_unate, binate;

  Abc_NtkForEachPo(pNtk, pObjPO, i) {

    pNtkConed = Abc_NtkCreateCone(pNtk, Abc_ObjFanin0(pObjPO), Abc_ObjName(pObjPO), 0);

    if (Abc_ObjFaninC0(pObjPO))
      Abc_NtkPo(pNtkConed, 0)->fCompl0 ^= 1;

    Abc_NtkForEachPi(pNtkConed, pObjPI, j)
    {
      id2name[Abc_ObjId(pObjPI)] = string(Abc_ObjName(pObjPI));
    }

    pMan = Abc_NtkToDar(pNtkConed, 0, 0);
    pCnf = Cnf_Derive(pMan, 1);

    // copy cnf
    pCnfdup = Cnf_DataDup(pCnf);
    Cnf_DataLift(pCnfdup, pCnf->nVars);

    pSat = (sat_solver *)Cnf_DataWriteIntoSolver(pCnf, 1, 0);

    sat_solver_setnvars(pSat, 2 * pCnf->nVars);
    for (int j = 0; j < pCnfdup->nClauses; ++j)
      sat_solver_addclause(pSat, pCnfdup->pClauses[j], pCnfdup->pClauses[j + 1]);

    // add po clauses
    add_po_clauses(pSat, pCnf, pCnfdup);

    //add pi clauses
    add_pi_clauses(pSat, pCnf, pCnfdup);
    
    lit assumption[Aig_ManCiNum(pMan) + 2];

    Aig_ManForEachCi(pMan, Aig_pObj, j) {

      int fvar = pCnf->pVarNums[Aig_ObjId(Aig_pObj)];
      int fneg_var = pCnfdup->pVarNums[Aig_ObjId(Aig_pObj)];

      //positive unate test
      //po assumption
      assumption[0] = toLitCond(fvar, 1);
      assumption[1] = toLitCond(fneg_var, 0);

      //pi assumption
      for (int k = 0; k < Aig_ManCiNum(pMan); ++k) {
        int enable_var = 2 * (pCnf->nVars) + k;
        assumption[k + 2] = (k == j) ? toLitCond(enable_var, 1) : toLitCond(enable_var, 0);
      }

      int pos_test = sat_solver_solve(pSat, assumption, assumption + Aig_ManCiNum(pMan) + 2, 0, 0, 0, 0);

      //negative unate test
      assumption[0] = toLitCond(fvar, 0);
      assumption[1] = toLitCond(fneg_var, 1);

      for (int k = 0; k < Aig_ManCiNum(pMan); ++k) {
        int enable_var = 2 * (pCnf->nVars) + k;
        assumption[k + 2] = (k == j) ? toLitCond(enable_var, 1) : toLitCond(enable_var, 0);
      }

      int neg_test = sat_solver_solve(pSat, assumption, assumption + Aig_ManCiNum(pMan) + 2, 0, 0, 0, 0);
      
      if (pos_test == l_False && neg_test == l_False) {
        ;
      }
      else if (pos_test == l_False) {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = '+';
        //cout << 'posunate' << endl;
      }
      else if (neg_test == l_False) {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = '-';
        //cout << 'negunate' << endl;
      }
      else {
        name2unate[id2name[Aig_ObjId(Aig_pObj)]] = 'b';
        //cout << 'binate' << endl;
      }
    }

    Abc_NtkForEachPi(pNtk, pObjPI, k)
    {
      if (name2unate.find(Abc_ObjName(pObjPI)) == name2unate.end()) {
        pos_unate.push_back(pObjPI);
        neg_unate.push_back(pObjPI);
      }
      else if (name2unate[Abc_ObjName(pObjPI)] == '+')
        pos_unate.push_back(pObjPI);
      else if (name2unate[Abc_ObjName(pObjPI)] == '-')
        neg_unate.push_back(pObjPI);
      else
        binate.push_back(pObjPI);
    }

    sort(neg_unate.begin(), neg_unate.end(), object_id_compare);
    sort(pos_unate.begin(), pos_unate.end(), object_id_compare);
    sort(binate.begin(), binate.end(), object_id_compare);

    //print
    cout << "node " << Abc_ObjName(pObjPO) << ":" << endl;

    print_unateness(pos_unate, neg_unate, binate);

    pos_unate.clear();
    neg_unate.clear();
    binate.clear();
    id2name.clear();
    name2unate.clear();
  }

  return 0;
}

/**CFile****************************************************************

  FileName    [dchSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [One round of SAT sweeping.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchSweep.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/
#include <pthread.h>
#include <stdint.h>
#include "dchInt.h"
#include "misc/bar/bar.h"
#define NUM_THREADS 8

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t * Dch_ObjChild0Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Dch_ObjFraig(Aig_ObjFanin0(pObj)), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t * Dch_ObjChild1Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Dch_ObjFraig(Aig_ObjFanin1(pObj)), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSweepNode( Dch_SimSat_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjRepr, * pObjFraig, * pObjFraig2, * pObjReprFraig;
    int RetValue;
    // get representative of this class
    pObjRepr = Aig_ObjRepr( p->pAigTotal, pObj );
    if ( pObjRepr == NULL )
        return;
    // get the fraiged node
    pObjFraig = Dch_ObjFraig( pObj );
    if ( pObjFraig == NULL )
        return;
    // get the fraiged representative
    pObjReprFraig = Dch_ObjFraig( pObjRepr );
    if ( pObjReprFraig == NULL )
        return;
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
    {
        // remember the proved equivalence
        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    assert( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pAigFraig) );
    RetValue = Dch_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
    if ( RetValue == -1 ) // timed out
    {
        Dch_ObjSetFraig( pObj, NULL );
        return;
    }
    if ( RetValue == 1 )  // proved equivalent
    {
        pObjFraig2 = Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
        Dch_ObjSetFraig( pObj, pObjFraig2 );
        // remember the proved equivalence
        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    // disproved the equivalence
    if ( p->pPars->fSimulateTfo )
        Dch_ManResimulateCex( p, pObj, pObjRepr );
    else
        Dch_ManResimulateCex2( p, pObj, pObjRepr );
}

typedef struct ManSweep_ThData_t_
{
    Dch_SimSat_t * pSimSat;
    Aig_Obj_t ** pLayeredObjs;
    int nStart;
    int nEnd;
    int fStart;
    int fDone;
    int fFinish;
    pthread_mutex_t Mutex;
    pthread_cond_t Cv;
} ManSweep_ThData_t;

void* ManSweep_WorkerThread(void *pArg)
{
    ManSweep_ThData_t *pThData = (ManSweep_ThData_t *)pArg;
    while (1) {
        pthread_mutex_lock(&pThData->Mutex);
        while (!pThData->fStart && !pThData->fFinish)
            pthread_cond_wait(&pThData->Cv, &pThData->Mutex);
        pThData->fStart = 0;
        pthread_mutex_unlock(&pThData->Mutex);
        if (pThData->fFinish) break;

        Dch_SimSat_t * pSimSat = pThData->pSimSat;
        Aig_Obj_t ** pLayeredObjs = pThData->pLayeredObjs;
        int Start = pThData->nStart, End = pThData->nEnd;

        memset(pSimSat->pReprsProved, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pSimSat->pAigTotal));
        for (int k = Start; k < End; k++)
        {
            Aig_Obj_t * pObj = pLayeredObjs[k];
            if (!pObj || !Aig_ObjIsNode(pObj)) continue;
            Dch_ManSweepNode( pSimSat, pObj );
        }

        pthread_mutex_lock(&pThData->Mutex);
        pThData->fDone = 1;
        pthread_mutex_unlock(&pThData->Mutex);
        pthread_cond_signal(&pThData->Cv);
    }
    return NULL;
}


int* pLayers;
int CmpNodes(const void * p1, const void * p2)
{
    const Aig_Obj_t * pObj1 = *(const Aig_Obj_t**)p1;
    const Aig_Obj_t * pObj2 = *(const Aig_Obj_t**)p2;
    if (!pObj1) return 1;
    if (!pObj2) return -1;
    return pLayers[pObj1->Id] - pLayers[pObj2->Id];
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSweep( Dch_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    // map constants and PIs
    p->pAigFraig = Aig_ManStart( Aig_ManObjNumMax(p->pAigTotal) );
    Aig_ManCleanData( p->pAigTotal );
    Aig_ManConst1(p->pAigTotal)->pData = Aig_ManConst1(p->pAigFraig);
    Aig_ManForEachCi( p->pAigTotal, pObj, i )
        pObj->pData = Aig_ObjCreateCi( p->pAigFraig );
    // sweep internal nodes
    pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAigTotal) );

    pthread_t WorkerThread[NUM_THREADS] = {};
    ManSweep_ThData_t ThData[NUM_THREADS] = {};
    for (int j = 0; j < NUM_THREADS; j++) {
        int status = pthread_create(&WorkerThread[j], NULL, ManSweep_WorkerThread, (void *)(&ThData[j]));
        assert(status == 0);
    }

    pLayers = ABC_CALLOC(int, Aig_ManObjNumMax(p->pAigTotal));
    Aig_Obj_t ** pLayeredObjs = ABC_CALLOC(Aig_Obj_t*, Aig_ManObjNumMax(p->pAigTotal));
    Aig_ManForEachNode( p->pAigTotal, pObj, i )
    {
        pLayeredObjs[i] = pObj;
        if (Aig_ObjFanin0(pObj) == NULL || Aig_ObjFanin1(pObj) == NULL) {
            continue;
        }
        Aig_Obj_t * pFanin0 = Aig_ObjFanin0(pObj);
        Aig_Obj_t * pFanin1 = Aig_ObjFanin1(pObj);
        pLayers[pObj->Id] = Abc_MaxInt(pLayers[pFanin0->Id], pLayers[pFanin1->Id]) + 1;
    }
    qsort(pLayeredObjs, Aig_ManObjNum(p->pAigTotal), sizeof(Aig_Obj_t*), CmpNodes);

    Vec_Int_t * vLayers = Vec_IntAlloc(100);
    Vec_IntPush(vLayers, 0);
    int LastLayer = 0;
    for (int i = 0; i < Aig_ManObjNumMax(p->pAigTotal); i++)
    {
        Aig_Obj_t * pObj = pLayeredObjs[i];
        if (!pObj || !Aig_ObjIsNode(pObj)) continue;
        int Layer = pLayers[pObj->Id];
        if (Layer > LastLayer) {
            LastLayer = Layer;
            Vec_IntPush(vLayers, i);
        }
    }

    Dch_SimSat_t * pSimSats = ABC_CALLOC(Dch_SimSat_t, NUM_THREADS);
    for (int j = 0; j < NUM_THREADS; j++) {
        pSimSats[j].pAigTotal = p->pAigTotal;
        pSimSats[j].pAigFraig = p->pAigFraig;
        pSimSats[j].pPars = p->pPars;
        pSimSats[j].ppClasses = p->ppClasses;

        pSimSats[j].pTravIds = ABC_CALLOC(int, Aig_ManObjNumMax(p->pAigTotal));
        pSimSats[j].pfMarkA = ABC_CALLOC(char, Aig_ManObjNumMax(p->pAigTotal));
        pSimSats[j].pfMarkB = ABC_CALLOC(char, Aig_ManObjNumMax(p->pAigTotal));
        pSimSats[j].nSatVars = 1;
        pSimSats[j].pSatVars = ABC_CALLOC(int, Aig_ManObjNumMax(p->pAigTotal));
        pSimSats[j].vSimRoots    = Vec_PtrAlloc( 1000 );
        pSimSats[j].vSimClasses  = Vec_PtrAlloc( 1000 );
        pSimSats[j].vUsedNodes   = Vec_PtrAlloc( 1000 );
        pSimSats[j].vFanins   = Vec_PtrAlloc( 1000 );
        pSimSats[j].pReprsProved = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAigTotal) );
    }

    int LayerStart;
    Vec_IntForEachEntry( vLayers, LayerStart, i )
    {
        int LayerEnd = Aig_ManObjNumMax(p->pAigTotal);
        if (i + 1 < Vec_IntSize(vLayers))
            LayerEnd = Vec_IntEntry(vLayers, i + 1);
        int LayerLen = LayerEnd - LayerStart;
        int Mt = LayerLen > NUM_THREADS * NUM_THREADS;

        for (int j = LayerStart; j < LayerEnd; j++)
        {
            Aig_Obj_t * pObj = pLayeredObjs[j];
            if (!pObj || !Aig_ObjIsNode(pObj)) continue;
            Bar_ProgressUpdate( pProgress, j, NULL );
            if ( Dch_ObjFraig(Aig_ObjFanin0(pObj)) == NULL ||
                 Dch_ObjFraig(Aig_ObjFanin1(pObj)) == NULL )
                continue;
            pObjNew = Aig_And( p->pAigFraig, Dch_ObjChild0Fra(pObj), Dch_ObjChild1Fra(pObj) );
            if ( pObjNew == NULL )
                continue;
            Dch_ObjSetFraig( pObj, pObjNew );
        }

        for (int j = 0; j < NUM_THREADS; j++) {
            pSimSats[j].vRefines = Vec_MemAlloc( sizeof(Dch_ClaRefine_t), 4 );
        }

        int SubLayerLen = (LayerLen + NUM_THREADS - 1) / NUM_THREADS;
        abctime clk = Abc_Clock();
        if (Mt) {
            printf("Running layer %d (%d nodes) on %d thread(s)\n", i, LayerLen, NUM_THREADS);
            for (int j = 0; j < NUM_THREADS; j++) {
                int Start = LayerStart + j * SubLayerLen;
                int End = Start + SubLayerLen;
                if (End > LayerEnd) End = LayerEnd;
                printf("  - sublayer: %d-%d\n", Start, End);
                ThData[j].pSimSat = &pSimSats[j];
                ThData[j].pLayeredObjs = pLayeredObjs;
                ThData[j].nStart = Start;
                ThData[j].nEnd = End;
                pthread_mutex_lock(&ThData[j].Mutex);
                ThData[j].fStart = 1;
                ThData[j].fDone = 0;
                pthread_mutex_unlock(&ThData[j].Mutex);
                pthread_cond_signal(&ThData[j].Cv);
            }
        } else {
            for (int k = LayerStart; k < LayerEnd; k++)
            {
                Aig_Obj_t * pObj = pLayeredObjs[k];
                if (!pObj || !Aig_ObjIsNode(pObj)) continue;
                Dch_ManSweepNode( &pSimSats[0], pObj );
            }
        }

        if (Mt) {
            for (int j = 0; j < NUM_THREADS; j++) {
                pthread_mutex_lock(&ThData[j].Mutex);
                while (!ThData[j].fDone) pthread_cond_wait(&ThData[j].Cv, &ThData[j].Mutex);
                pthread_mutex_unlock(&ThData[j].Mutex);
                if (j > 0)
                    for (int k = 0; k < Aig_ManObjNumMax(p->pAigTotal); k++)
                        if (pSimSats[j].pReprsProved[k])
                            pSimSats[0].pReprsProved[k] = pSimSats[j].pReprsProved[k];
            }
        }
        for (int j = 0; j < NUM_THREADS; j++) {
            int k;
            word* pEntry;
            Vec_MemForEachEntry( pSimSats[j].vRefines, pEntry, k ) {
                Dch_ClaRefine_t * pRefine = (Dch_ClaRefine_t *) pEntry;
                if (pRefine->pRepr) {
                    Dch_ClassesRefineOneClassRefine(p->ppClasses, pRefine->vClassOld, pRefine->vClassNew, pRefine->pRepr);
                    Vec_PtrFree(pRefine->vClassOld);
                } else {
                    Dch_ClassesRefineConst1GroupRefine(p->ppClasses, pRefine->vClassNew);
                }
                Vec_PtrFree(pRefine->vClassNew);
            }
            Vec_MemFree( pSimSats[j].vRefines );
        }
        if (Mt) {
            printf("- done in %ld ns\n", Abc_Clock() - clk);
        }
    }

    Vec_IntFree(vLayers);
    ABC_FREE(pLayers);
    ABC_FREE(pLayeredObjs);

    for (int j = 0; j < NUM_THREADS; j++) {
        pthread_mutex_lock(&ThData[j].Mutex);
        ThData[j].fFinish = 1;
        pthread_mutex_unlock(&ThData[j].Mutex);
        pthread_cond_signal(&ThData[j].Cv);
        pthread_join(WorkerThread[j], NULL);
        if (pSimSats[j].pSat) sat_solver_delete( pSimSats[j].pSat );
        ABC_FREE(pSimSats[j].pTravIds);
        ABC_FREE(pSimSats[j].pfMarkA);
        ABC_FREE(pSimSats[j].pfMarkB);
        ABC_FREE(pSimSats[j].pSatVars);
        Vec_PtrFree(pSimSats[j].vSimRoots);
        Vec_PtrFree(pSimSats[j].vSimClasses);
        Vec_PtrFree(pSimSats[j].vUsedNodes);
        Vec_PtrFree(pSimSats[j].vFanins);
        p->nSatVars += pSimSats[j].nSatVars;
        if (j > 0) ABC_FREE(pSimSats[j].pReprsProved);
    }

    Bar_ProgressStop( pProgress );
    // update the representatives of the nodes (makes classes invalid)
    ABC_FREE( p->pAigTotal->pReprs );
    p->pAigTotal->pReprs = pSimSats[0].pReprsProved;

    ABC_FREE(pSimSats);

    // clean the mark
    Aig_ManCleanMarkB( p->pAigTotal );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END


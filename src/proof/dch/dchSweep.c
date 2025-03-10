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
#include <stdint.h>
#include "dchInt.h"
#include "misc/bar/bar.h"
#define NUM_THREADS 2

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
    assert( Aig_ObjRepr( p->pAigTotal, pObj ) != pObjRepr );
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

    Aig_Obj_t ** pReprsProved = ABC_CALLOC(Aig_Obj_t*, Aig_ManObjNumMax(p->pAigTotal));
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

    Dch_SimSat_t * pSimSat = ABC_CALLOC(Dch_SimSat_t, NUM_THREADS);
    for (int j = 0; j < NUM_THREADS; j++) {
        pSimSat[j].pAigTotal = p->pAigTotal;
        pSimSat[j].pAigFraig = p->pAigFraig;
        pSimSat[j].pPars = p->pPars;
        pSimSat[j].ppClasses = p->ppClasses;
        pSimSat[j].vFanins = p->vFanins;

        pSimSat[j].nSatVars = 1;
        pSimSat[j].pSatVars = ABC_CALLOC(int, Aig_ManObjNumMax(p->pAigTotal));
        pSimSat[j].vSimRoots    = Vec_PtrAlloc( 1000 );
        pSimSat[j].vSimClasses  = Vec_PtrAlloc( 1000 );
        pSimSat[j].vUsedNodes   = Vec_PtrAlloc( 1000 );
        pSimSat[j].pReprsProved = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p->pAigTotal) );
    }

    int LayerStart;
    Vec_IntForEachEntry( vLayers, LayerStart, i )
    {
        for (int j = 0; j < NUM_THREADS; j++)
            memset(pSimSat[j].pReprsProved, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p->pAigTotal));

        int LayerEnd = Aig_ManObjNumMax(p->pAigTotal);
        if (i + 1 < Vec_IntSize(vLayers))
            LayerEnd = Vec_IntEntry(vLayers, i + 1);
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

        for (int j = LayerStart; j < LayerEnd; j++)
        {
            Aig_Obj_t * pObj = pLayeredObjs[j];
            if (!pObj || !Aig_ObjIsNode(pObj)) continue;
            Dch_ManSweepNode( &pSimSat[0], pObj );
        }

        for (int j = 0; j < NUM_THREADS; j++)
            for (int k = 0; k < Aig_ManObjNumMax(p->pAigTotal); k++)
                if (pSimSat[j].pReprsProved[k])
                    pReprsProved[k] = pSimSat[j].pReprsProved[k];
    }

    Vec_IntFree(vLayers);
    ABC_FREE(pLayers);
    ABC_FREE(pLayeredObjs);

    for (int j = 0; j < NUM_THREADS; j++) {
        if (pSimSat[j].pSat) sat_solver_delete( pSimSat[j].pSat );
        ABC_FREE(pSimSat[j].pSatVars);
        Vec_PtrFree(pSimSat[j].vSimRoots);
        Vec_PtrFree(pSimSat[j].vSimClasses);
        Vec_PtrFree(pSimSat[j].vUsedNodes);
        p->nSatVars += pSimSat[j].nSatVars;
        ABC_FREE(pSimSat[j].pReprsProved);
    }
    ABC_FREE(pSimSat);

    Bar_ProgressStop( pProgress );
    // update the representatives of the nodes (makes classes invalid)
    ABC_FREE( p->pAigTotal->pReprs );
    p->pAigTotal->pReprs = pReprsProved;
    // clean the mark
    Aig_ManCleanMarkB( p->pAigTotal );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END


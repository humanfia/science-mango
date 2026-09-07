import Family8Grounding.Family8ParentwiseCrossingIntegratedSuccessorV1
import Family8Grounding.Family8ExactDef212CompositionalParentsV1
import Family8Grounding.Family8ContractedJohnEighthProxyCarrierMonoV1
import Family8Grounding.Family8ContractedJohnEighthProxyTopContainingTubeV1
import Mathlib.Tactic

/-!
# A faithful coherent successor for both children of a parentwise crossing

The two children of the crossing have different geometric transports.  The
same-`q` child uses the actual contracted-John/eighth proxy, while the active
parent child uses only the common eighth normalization.  This module keeps
those routes separate and attaches each literal child family to its own real
coherent cover and exact Definition 2.12 input package.

No cover is manufactured here: in particular, the canonical identity-radius
cover is not used.  Instead, the readiness package requires the parent tube at
every transported source scale to be the corresponding real proxy tube.  The
only geometric facts not supplied by the present source hierarchy are the two
normalized-axis inclusions; they remain explicit inputs and produce literal
carrier nesting through `Metric.cthickening` monotonicity.  The parent `q` is
always the one already stored in the crossing successor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedFiberFaithfulCoherentSuccessorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnEighthProxyCarrierMonoV1
open Family8ContractedJohnEighthProxyCarrierNestingV1
open Family8ContractedJohnEighthProxyTopContainingTubeV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ExactDef212CompositionalParentsV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SelectedFiberJohnCanonicalCoherentFactorV1
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8TubeJohnUnitRescalingGeometryLeOneV7
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}

/-- The source-scale lower bound needed repeatedly below. -/
theorem crossingDeltaLeRho
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    delta <= W.rho :=
  (S.delta_le_tau W.m).trans (crossingTauLeRho W)

/-- The literal selected root tube.  This definition never selects a new
parent. -/
def crossingRootTube
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) : Tube W.rho :=
  (crossingBaseCover W).coarse.tubes (crossingBaseQ W).1

/-- The John witness already attached to the same selected root. -/
def crossingRootJohnWitness
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    JohnAxisWitness (crossingRootTube W).body :=
  StickyScaleCover.tubeJohnWitnessLeOne
    (crossingBaseCover W) (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W)

/-- The actual q-fresh scale corresponding to a source scale `tau`. -/
def qFreshProxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) (tau : NNReal) : NNReal :=
  contractedJohnProxyRadius tau W.rho / 8

/-- The actual active-parent scale corresponding to a source scale
`sigma`. -/
def activeParentProxyScale (sigma : NNReal) : NNReal :=
  sigma / 8

theorem qFreshChildRadius_le_proxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {tau : NNReal} (hdeltaTau : delta <= tau) :
    badParentFreshChildRadius delta W.rho <= qFreshProxyScale W tau := by
  exact contractedJohnEighthProxyRadius_mono hdeltaTau

theorem qFreshProxyScale_le_one
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {tau : NNReal} (hTauRho : tau <= W.rho) :
    qFreshProxyScale W tau <= 1 :=
  contractedJohnEighthProxyRadius_le_one (crossingRhoPos W) hTauRho

theorem activeParentChildRadius_le_proxyScale
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    {sigma : NNReal} (hRhoSigma : W.rho <= sigma) :
    W.rho / 8 <= activeParentProxyScale sigma := by
  unfold activeParentProxyScale
  gcongr

theorem activeParentProxyScale_le_one
    {sigma : NNReal} (hSigmaOne : sigma <= 1) :
    activeParentProxyScale sigma <= 1 := by
  calc
    activeParentProxyScale sigma <= activeParentProxyScale 1 := by
      unfold activeParentProxyScale
      gcongr
    _ <= 1 := by
      change (1 : Real) / 8 <= 1
      norm_num

/-- The actual source ancestor of a selected fine tube at scale `tau`. -/
def qFreshSourceAncestorTube
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (tau : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= W.rho)
    (i : {j // j ∈ X.dualChild.qFibreSelected}) : Tube tau :=
  let T := C.base.cover tau hdeltaTau
    (hTauRho.trans (crossingRhoLeOne W))
  T.coarse.tubes (T.parent i.1.1)

/-- The source ancestor of a selected active parent at scale `sigma`. -/
def activeParentSourceAncestorTube
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (sigma : NNReal) (hRhoSigma : W.rho <= sigma)
    (hSigmaOne : sigma <= 1)
    (i : {k // k ∈ X.dualChild.activeParentSelected}) : Tube sigma :=
  let U := C.base.cover sigma
    ((crossingDeltaLeRho W).trans hRhoSigma) hSigmaOne
  U.coarse.tubes
    (C.parent W.rho sigma (crossingDeltaLeRho W)
      hRhoSigma hSigmaOne i.1.1)

/-- The q-fresh fine family is definitionally the genuine normalized proxy
family on the same selected subtype. -/
@[simp] theorem qFibreChildDatum_family_tubes
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (i : {j // j ∈ X.dualChild.qFibreSelected}) :
    X.dualChild.qFibreChildDatum.family.tubes i =
      contractedJohnEighthProxyTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (D.family.tubes i.1.1) := by
  rfl

/-- The active-parent fine family is definitionally the genuine eighth
normalization of the same selected source parents. -/
@[simp] theorem activeParentChildDatum_family_tubes
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (i : {k // k ∈ X.dualChild.activeParentSelected}) :
    X.dualChild.activeParentChildDatum.family.tubes i =
      eighthNormalizedTube
        ((crossingBaseCover W).coarse.tubes i.1.1) := by
  rfl

/-- Real eighth-normalized nesting for the active-parent route. -/
structure EighthNormalizedActualHierarchyStep
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma) : Prop where
  source_scale_le : rho <= sigma
  source_carrier_subset : T.carrier ⊆ U.carrier
  normalized_axis_subset :
    (eighthNormalizedTube T).axis.carrier ⊆
      (eighthNormalizedTube U).axis.carrier
  actual_carrier_subset :
    (eighthNormalizedTube T).carrier ⊆
      (eighthNormalizedTube U).carrier

theorem eighthNormalizedActualHierarchyStep_of_axis_subset
    {rho sigma : NNReal} (T : Tube rho) (U : Tube sigma)
    (hRhoSigma : rho <= sigma) (hTU : T.carrier ⊆ U.carrier)
    (haxis :
      (eighthNormalizedTube T).axis.carrier ⊆
        (eighthNormalizedTube U).axis.carrier) :
    EighthNormalizedActualHierarchyStep T U where
  source_scale_le := hRhoSigma
  source_carrier_subset := hTU
  normalized_axis_subset := haxis
  actual_carrier_subset :=
    tube_carrier_subset_of_axis_subset_of_radius_le
      (eighthNormalizedTube T) (eighthNormalizedTube U) haxis (by gcongr)

/-- Exact Definition 2.12 on the source cover identifies the intermediate
parent with the same selected `q`; the explicit axis inclusion then closes
the real proxy carrier step. -/
theorem qFresh_sourceHierarchyStep_of_axis_subset
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    {sourceK : NNReal} (H : ExactScaleDef212Inputs C.base sourceK)
    (tau : NNReal) (hdeltaTau : delta <= tau)
    (hTauRho : tau <= W.rho)
    (i : {j // j ∈ X.dualChild.qFibreSelected})
    (haxis :
      (contractedJohnEighthProxyTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (D.family.tubes i.1.1)).axis.carrier ⊆
      (contractedJohnEighthProxyTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)).axis.carrier) :
    ContractedJohnEighthActualHierarchyStep (crossingRootTube W)
      (crossingRhoPos W) (crossingRootJohnWitness W)
      (D.family.tubes i.1.1)
      (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i) := by
  let T := C.base.cover tau hdeltaTau
    (hTauRho.trans (crossingRhoLeOne W))
  let R := crossingBaseCover W
  have hfiber : i.1.1 ∈ R.fiber (crossingBaseQ W).1 := i.1.2
  have hiData := (R.mem_fiber i.1.1 (crossingBaseQ W).1).1 hfiber
  have hiT : i.1.1 ∈ T.activeFine := by
    rw [T.activeFine_eq_refined, ← R.activeFine_eq_refined]
    exact hiData.1
  have hTU :
      (D.family.tubes i.1.1).carrier ⊆
        (T.coarse.tubes (T.parent i.1.1)).carrier :=
    T.carrier_subset i.1.1 hiT
  have hparentMem : T.parent i.1.1 ∈ T.activeCoarse :=
    T.parent_mem i.1.1 hiT
  have hcompat :=
    fine_parent_compatible_of_doubledParentPartitioning
      C tau W.rho hdeltaTau hTauRho (crossingRhoLeOne W)
      (H.doubled_parent_partitioning W.rho
        (hdeltaTau.trans hTauRho) (crossingRhoLeOne W))
      i.1.1 hiT
  have hparent :
      C.parent tau W.rho hdeltaTau hTauRho (crossingRhoLeOne W)
          (T.parent i.1.1) = (crossingBaseQ W).1 :=
    hcompat.symm.trans hiData.2
  have hUP := C.carrier_subset tau W.rho hdeltaTau hTauRho
    (crossingRhoLeOne W) (T.parent i.1.1) hparentMem
  change (T.coarse.tubes (T.parent i.1.1)).carrier ⊆
    (R.coarse.tubes
      (C.parent tau W.rho hdeltaTau hTauRho
        (crossingRhoLeOne W) (T.parent i.1.1))).carrier at hUP
  rw [hparent] at hUP
  exact contractedJohnEighthActualHierarchyStep_of_axis_subset
    (crossingRootTube W) (crossingRhoPos W) (crossingRootJohnWitness W)
    (D.family.tubes i.1.1)
    (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
    hdeltaTau hTauRho hTU hUP haxis

/-- The source coherent cover supplies active-parent containment; the only
additional geometry needed by eighth normalization is the displayed axis
inclusion. -/
theorem activeParent_sourceHierarchyStep_of_axis_subset
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (sigma : NNReal) (hRhoSigma : W.rho <= sigma)
    (hSigmaOne : sigma <= 1)
    (i : {k // k ∈ X.dualChild.activeParentSelected})
    (haxis :
      (eighthNormalizedTube
        ((crossingBaseCover W).coarse.tubes i.1.1)).axis.carrier ⊆
      (eighthNormalizedTube
        (activeParentSourceAncestorTube W X sigma hRhoSigma
          hSigmaOne i)).axis.carrier) :
    EighthNormalizedActualHierarchyStep
      ((crossingBaseCover W).coarse.tubes i.1.1)
      (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i) := by
  have hTU := C.carrier_subset W.rho sigma
    (crossingDeltaLeRho W) hRhoSigma hSigmaOne i.1.1 i.1.2
  exact eighthNormalizedActualHierarchyStep_of_axis_subset
    ((crossingBaseCover W).coarse.tubes i.1.1)
    (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)
    hRhoSigma hTU haxis

/-- Positive data still required to realize the two transported child
hierarchies.  Both covers are typed on the literal child families.  The two
`parent_realizes_source` fields prevent an unrelated/identity hierarchy from
being substituted: at every transported scale, the chosen actual parent is
the corresponding geometric source ancestor. -/
structure FaithfulCoherentSuccessorReadiness
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  sourceK : NNReal
  sourceExact : ExactScaleDef212Inputs C.base sourceK
  qFreshCover :
    CoherentStickyMultiscaleCover X.dualChild.qFibreChildDatum.family
  qFreshK : NNReal
  qFreshExact : ExactScaleDef212Inputs qFreshCover.base qFreshK
  activeParentCover :
    CoherentStickyMultiscaleCover X.dualChild.activeParentChildDatum.family
  activeParentK : NNReal
  activeParentExact :
    ExactScaleDef212Inputs activeParentCover.base activeParentK
  qFresh_axis_subset : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    (contractedJohnEighthProxyTube (crossingRootTube W)
      (crossingRhoPos W) (crossingRootJohnWitness W)
      (D.family.tubes i.1.1)).axis.carrier ⊆
    (contractedJohnEighthProxyTube (crossingRootTube W)
      (crossingRhoPos W) (crossingRootJohnWitness W)
      (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)).axis.carrier
  activeParent_axis_subset : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    (eighthNormalizedTube
      ((crossingBaseCover W).coarse.tubes i.1.1)).axis.carrier ⊆
    (eighthNormalizedTube
      (activeParentSourceAncestorTube W X sigma hRhoSigma
        hSigmaOne i)).axis.carrier
  qFresh_parent_realizes_source : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    let A := qFreshCover.base.cover (qFreshProxyScale W tau)
      (qFreshChildRadius_le_proxyScale W hdeltaTau)
      (qFreshProxyScale_le_one W hTauRho)
    A.coarse.tubes (A.parent i) =
      contractedJohnEighthProxyTube (crossingRootTube W)
        (crossingRhoPos W) (crossingRootJohnWitness W)
        (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
  activeParent_parent_realizes_source : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    let A := activeParentCover.base.cover (activeParentProxyScale sigma)
      (activeParentChildRadius_le_proxyScale W hRhoSigma)
      (activeParentProxyScale_le_one hSigmaOne)
    A.coarse.tubes (A.parent i) =
      eighthNormalizedTube
        (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)

/-- The completed positive connector.  Composition comes from exact
Definition 2.12; source-to-proxy carrier steps come from the explicit axis
inputs above. -/
structure SelectedFiberFaithfulCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W) where
  readiness : FaithfulCoherentSuccessorReadiness W X
  source_compositional : HasCompositionalParents C
  qFresh_compositional : HasCompositionalParents readiness.qFreshCover
  activeParent_compositional :
    HasCompositionalParents readiness.activeParentCover
  qFresh_source_steps : forall (tau : NNReal)
      (hdeltaTau : delta <= tau) (hTauRho : tau <= W.rho)
      (i : {j // j ∈ X.dualChild.qFibreSelected}),
    ContractedJohnEighthActualHierarchyStep (crossingRootTube W)
      (crossingRhoPos W) (crossingRootJohnWitness W)
      (D.family.tubes i.1.1)
      (qFreshSourceAncestorTube W X tau hdeltaTau hTauRho i)
  activeParent_source_steps : forall (sigma : NNReal)
      (hRhoSigma : W.rho <= sigma) (hSigmaOne : sigma <= 1)
      (i : {k // k ∈ X.dualChild.activeParentSelected}),
    EighthNormalizedActualHierarchyStep
      ((crossingBaseCover W).coarse.tubes i.1.1)
      (activeParentSourceAncestorTube W X sigma hRhoSigma hSigmaOne i)

/-- Assemble the faithful connector without choosing a cover or a parent.
Every object comes from the supplied positive readiness. -/
theorem exists_selectedFiberFaithfulCoherentSuccessor
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (X : ParentwiseCrossingIntegratedSuccessor W)
    (R : FaithfulCoherentSuccessorReadiness W X) :
    Nonempty (SelectedFiberFaithfulCoherentSuccessor W X) := by
  exact ⟨
    { readiness := R
      source_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs C R.sourceExact
      qFresh_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs
          R.qFreshCover R.qFreshExact
      activeParent_compositional :=
        hasCompositionalParents_of_exactScaleDef212Inputs
          R.activeParentCover R.activeParentExact
      qFresh_source_steps := fun tau hdeltaTau hTauRho i =>
        qFresh_sourceHierarchyStep_of_axis_subset W X R.sourceExact
          tau hdeltaTau hTauRho i
          (R.qFresh_axis_subset tau hdeltaTau hTauRho i)
      activeParent_source_steps := fun sigma hRhoSigma hSigmaOne i =>
        activeParent_sourceHierarchyStep_of_axis_subset W X
          sigma hRhoSigma hSigmaOne i
          (R.activeParent_axis_subset sigma hRhoSigma hSigmaOne i) }⟩

namespace SelectedFiberFaithfulCoherentSuccessor

variable {W : FirstParentwiseNormalizedCrossingWitness
  D hD C S epsilon hepsilon eta N}
  {X : ParentwiseCrossingIntegratedSuccessor W}

/-- Literal carrier nesting in the real q-fresh coherent cover. -/
theorem qFresh_cover_carrier_subset
    (Y : SelectedFiberFaithfulCoherentSuccessor W X)
    (r s : NNReal)
    (hchildR : badParentFreshChildRadius delta W.rho <= r)
    (hRS : r <= s) (hSOne : s <= 1)
    (i : Fin ((Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).coarseCard))
    (hi : i ∈ (Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).activeCoarse) :
    ((Y.readiness.qFreshCover.base.cover r hchildR
      (hRS.trans hSOne)).coarse.tubes i).carrier ⊆
    ((Y.readiness.qFreshCover.base.cover s (hchildR.trans hRS)
      hSOne).coarse.tubes
        (Y.readiness.qFreshCover.parent r s hchildR hRS hSOne i)).carrier :=
  Y.readiness.qFreshCover.carrier_subset r s hchildR hRS hSOne i hi

/-- Literal carrier nesting in the real active-parent coherent cover. -/
theorem activeParent_cover_carrier_subset
    (Y : SelectedFiberFaithfulCoherentSuccessor W X)
    (r s : NNReal) (hchildR : W.rho / 8 <= r)
    (hRS : r <= s) (hSOne : s <= 1)
    (i : Fin ((Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).coarseCard))
    (hi : i ∈ (Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).activeCoarse) :
    ((Y.readiness.activeParentCover.base.cover r hchildR
      (hRS.trans hSOne)).coarse.tubes i).carrier ⊆
    ((Y.readiness.activeParentCover.base.cover s
      (hchildR.trans hRS) hSOne).coarse.tubes
        (Y.readiness.activeParentCover.parent r s hchildR
          hRS hSOne i)).carrier :=
  Y.readiness.activeParentCover.carrier_subset
    r s hchildR hRS hSOne i hi

end SelectedFiberFaithfulCoherentSuccessor

#print axioms crossingDeltaLeRho
#print axioms qFibreChildDatum_family_tubes
#print axioms activeParentChildDatum_family_tubes
#print axioms EighthNormalizedActualHierarchyStep
#print axioms eighthNormalizedActualHierarchyStep_of_axis_subset
#print axioms qFresh_sourceHierarchyStep_of_axis_subset
#print axioms activeParent_sourceHierarchyStep_of_axis_subset
#print axioms FaithfulCoherentSuccessorReadiness
#print axioms SelectedFiberFaithfulCoherentSuccessor
#print axioms exists_selectedFiberFaithfulCoherentSuccessor
#print axioms SelectedFiberFaithfulCoherentSuccessor.qFresh_cover_carrier_subset

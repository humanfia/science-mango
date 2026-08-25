import FamilyStickyGrounding.FamilyStickyScaleChainArbitraryRadiusInterpolationV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

open MeasureTheory
namespace FamilyStickyScaleChainArbitraryRadiusBoundsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Adjacent-scale coherence and arbitrary-radius sticky bounds

The structure below is the residual local geometry left after using the
existing coherent-cover construction.  Its fields compare only one
intermediate cover with the upper endpoint of the adjacent finite interval.
They do not contain an at-every-scale Frostman or Katz--Tao assertion.

For Frostman interpolation, parent compatibility identifies the larger
endpoint fiber containing an intermediate fiber.  Subfamily monotonicity at
a common test body is automatic from the induced subtype embedding; the only
extra Frostman input is the reverse comparison of the parent normalizers.
For Katz--Tao interpolation, the already formalized parent-mass and
thickened-body inputs produce the coarse concentration comparison theorem.
-/

variable {delta : NNReal} {depth : Nat} {epsilon : Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FiniteScaleSequence delta depth)

/-- Minimal local coherence on every large adjacent interval.  Parent and
carrier data themselves come from `C`; the first field says those parents
also agree with the original fine-index parent assignments. -/
structure LargeIntervalCoverCoherence (epsilon : Real)
    (frostmanLoss katzTaoLoss massLoss bodyLoss : ENNReal) : Prop where
  parent_compatible : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : iota),
    i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)
  fiber_parent_concentration_le : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      forall k : Fin
        (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard,
      k ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse ->
        concentration
            ((upperEndpointCover C S m).fiberFamily
              ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k))
            ((upperEndpointCover C S m).coarse.tubes
              ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).body <=
          frostmanLoss *
            concentration
              ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
              ((lowerScaleCover C S m rho hTauRho hRhoTheta).coarse.tubes k).body
  parentFiberMass : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      ParentFiberMassMonotonicity
        (rhoToUpperCover C S m rho hTauRho hRhoTheta) massLoss
  thickeningVolume : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    S.IsLarge epsilon m ->
      CapturingThickeningVolumeControl
        (rhoToUpperCover C S m rho hTauRho hRhoTheta) bodyLoss
  katzTaoLoss_bound : massLoss * bodyLoss <= katzTaoLoss

/-- The lower fine fiber is literally included in the endpoint fine fiber.
This is the set-level consequence of parent composition. -/
theorem lower_fiber_subset_upper_fiber
    {frostmanLoss katzTaoLoss massLoss bodyLoss : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard) :
    (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber k ⊆
      (upperEndpointCover C S m).fiber
        ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k) := by
  intro i hi
  have hiLower :=
    ((lowerScaleCover C S m rho hTauRho hRhoTheta).mem_fiber i k).1 hi
  apply ((upperEndpointCover C S m).mem_fiber i
    ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).2
  constructor
  · rw [(upperEndpointCover C S m).activeFine_eq_refined]
    rw [(lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine_eq_refined]
      at hiLower
    exact hiLower.1
  · rw [D.parent_compatible m rho hTauRho hRhoTheta i hiLower.1,
      hiLower.2]
/-- Reindexing a convex family along an embedding cannot increase its
contained mass or its concentration. -/
theorem concentration_le_of_embedding
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (F : ConvexFamily alpha) (G : ConvexFamily beta)
    (e : alpha ↪ beta) (hbody : forall a, F a = G (e a))
    (K : ConvexBody Space) :
    concentration F K <= concentration G K := by
  classical
  rw [concentration_eq_containedMass_div,
    concentration_eq_containedMass_div]
  gcongr
  unfold containedMass
  calc
    (∑ a ∈ containedIndices F K, volume (F a : Set Space)) =
        ∑ a ∈ containedIndices F K, volume (G (e a) : Set Space) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [hbody a]
    _ = ∑ b ∈ (containedIndices F K).image e,
        volume (G b : Set Space) := by
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      exact e.injective hab
    _ <= ∑ b ∈ containedIndices G K, volume (G b : Set Space) := by
      apply Finset.sum_le_sum_of_subset
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rw [mem_containedIndices] at ha ⊢
      simpa only [hbody a] using ha

/-- Parent composition induces an embedding of an intermediate fiber into
the upper endpoint fiber.  Since both fiber families retain the same original
fine body, concentration monotonicity at a common test body is automatic. -/
theorem lower_fiber_concentration_le_upper_fiber
    {frostmanLoss katzTaoLoss massLoss bodyLoss : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (K : ConvexBody Space) :
    concentration
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) K <=
      concentration
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) K := by
  let e :
      {i // i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber k} ↪
        {i // i ∈ (upperEndpointCover C S m).fiber
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)} :=
    { toFun := fun i => ⟨i.1,
        lower_fiber_subset_upper_fiber C S D m rho hTauRho hRhoTheta k i.2⟩
      inj' := fun a b hab => by
        apply Subtype.ext
        exact congrArg (fun x => x.1) hab }
  exact concentration_le_of_embedding
    ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
    ((upperEndpointCover C S m).fiberFamily
      ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k))
    e (fun _ => rfl) K


/-- Endpoint hypotheses on every finite adjacent interval, together with the
actual all-large certificate used to activate the local coherence fields. -/
structure DiscreteAllLargeStickyBounds (epsilon : Real)
    (frostmanError katzTaoError : ENNReal) : Prop where
  all_large : S.AllStepsLarge epsilon
  frostman_endpoint : forall m : Fin depth,
    (upperEndpointCover C S m).IsFrostmanAtScale frostmanError
  katzTao_endpoint : forall m : Fin depth,
    (upperEndpointCover C S m).IsKatzTaoAtScale katzTaoError

/-! ## Fixed-interval transfer -/

/-- A discrete Frostman bound at the upper endpoint transfers to every
radius in the same large adjacent interval. -/
theorem isFrostmanAtScale_of_upperEndpoint
    {frostmanLoss katzTaoLoss massLoss bodyLoss
      frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    (lowerScaleCover C S m rho hTauRho hRhoTheta).IsFrostmanAtScale
      (frostmanLoss * frostmanError) := by
  intro k hk K hK
  let L := lowerScaleCover C S m rho hTauRho hRhoTheta
  let U := upperEndpointCover C S m
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  have hkU : I.parent k ∈ U.activeCoarse := I.parent_mem k hk
  have hKUpper : (K : Set Space) ⊆ (U.coarse.tubes (I.parent k)).carrier :=
    hK.trans (I.carrier_subset k hk)
  calc
    concentration (L.fiberFamily k) K <=
        concentration (U.fiberFamily (I.parent k)) K :=
      lower_fiber_concentration_le_upper_fiber C S D m rho hTauRho hRhoTheta k K
    _ <= frostmanError *
        concentration (U.fiberFamily (I.parent k))
          (U.coarse.tubes (I.parent k)).body :=
      B.frostman_endpoint m (I.parent k) hkU K hKUpper
    _ <= frostmanError *
        (frostmanLoss *
          concentration (L.fiberFamily k) (L.coarse.tubes k).body) := by
      gcongr
      exact D.fiber_parent_concentration_le m rho hTauRho hRhoTheta
        (B.all_large m) k hk
    _ = (frostmanLoss * frostmanError) *
        concentration (L.fiberFamily k) (L.coarse.tubes k).body := by
      ac_rfl

/-- The actual nested-cover geometry transfers the discrete endpoint
Katz--Tao bound to every radius in the same large adjacent interval. -/
theorem isKatzTaoAtScale_of_upperEndpoint
    {frostmanLoss katzTaoLoss massLoss bodyLoss
      frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    (lowerScaleCover C S m rho hTauRho hRhoTheta).IsKatzTaoAtScale
      (katzTaoLoss * katzTaoError) := by
  apply (StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
    (lowerScaleCover C S m rho hTauRho hRhoTheta) _).2
  have hlocal := FamilyStickyScaleChainCoherentMassLocalizationProducerV1.CoherentStickyMultiscaleCover.actualCoarseDeltaMaxAt_le_of_nestedGeometry C
    rho (S.theta m) ((S.delta_le_tau m).trans hTauRho)
    hRhoTheta (S.theta_le_one m) massLoss bodyLoss
    (D.parentFiberMass m rho hTauRho hRhoTheta (B.all_large m))
    (D.thickeningVolume m rho hTauRho hRhoTheta (B.all_large m))
  have hendpoint :
      StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base (S.theta m) <=
        katzTaoError := by
    rw [StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq C.base
      (S.theta m) ((S.delta_le_tau m).trans (S.tau_le_theta m))
      (S.theta_le_one m)]
    exact (StickyScaleCover.isKatzTaoAtScale_iff_coarseDeltaMax_le
      (upperEndpointCover C S m) katzTaoError).1 (B.katzTao_endpoint m)
  calc
    coarseDeltaMax (lowerScaleCover C S m rho hTauRho hRhoTheta) =
        StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base rho := by
      simpa only [lowerScaleCover] using
        (StickyMultiscaleCover.actualCoarseDeltaMaxAt_eq C.base rho
          ((S.delta_le_tau m).trans hTauRho)
          (hRhoTheta.trans (S.theta_le_one m))).symm
    _ <= (massLoss * bodyLoss) *
        StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base (S.theta m) :=
      hlocal
    _ <= katzTaoLoss *
        StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base (S.theta m) := by
      gcongr
      exact D.katzTaoLoss_bound
    _ <= katzTaoLoss * katzTaoError := by
      gcongr

/-! ## Arbitrary-radius consequences -/

/-- Canonical nearest-interval interpolation gives Frostman at every radius. -/
theorem isFrostmanAtEveryScale_of_discreteAllLarge
    (hdepth : 0 < depth)
    {frostmanLoss katzTaoLoss massLoss bodyLoss
      frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    C.base.IsFrostmanAtEveryScale (frostmanLoss * frostmanError) := by
  intro rho hdelta hrho
  let m := FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.nearestInterval S hdepth rho hdelta
  have hTauRho : S.tau m <= rho :=
    FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.tau_nearestInterval_le S hdepth rho hdelta hrho
  have hRhoTheta : rho <= S.theta m :=
    FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.le_theta_nearestInterval S hdepth rho hdelta hrho
  simpa only [lowerScaleCover] using
    isFrostmanAtScale_of_upperEndpoint C S D B m rho hTauRho hRhoTheta

/-- Canonical nearest-interval interpolation gives Katz--Tao at every radius. -/
theorem isKatzTaoAtEveryScale_of_discreteAllLarge
    (hdepth : 0 < depth)
    {frostmanLoss katzTaoLoss massLoss bodyLoss
      frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    C.base.IsKatzTaoAtEveryScale (katzTaoLoss * katzTaoError) := by
  intro rho hdelta hrho
  let m := FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.nearestInterval S hdepth rho hdelta
  have hTauRho : S.tau m <= rho :=
    FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.tau_nearestInterval_le S hdepth rho hdelta hrho
  have hRhoTheta : rho <= S.theta m :=
    FamilyStickyScaleChainArbitraryRadiusInterpolationV1.FiniteScaleSequence.le_theta_nearestInterval S hdepth rho hdelta hrho
  simpa only [lowerScaleCover] using
    isKatzTaoAtScale_of_upperEndpoint C S D B m rho hTauRho hRhoTheta

/-- Both paper conditions are obtained on the same chosen multiscale cover. -/
theorem isStickyAtEveryScale_of_discreteAllLarge
    (hdepth : 0 < depth)
    {frostmanLoss katzTaoLoss massLoss bodyLoss
      frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalCoverCoherence C S epsilon
      frostmanLoss katzTaoLoss massLoss bodyLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError) :
    C.base.IsStickyAtEveryScale
      (frostmanLoss * frostmanError) (katzTaoLoss * katzTaoError) := by
  exact ⟨isFrostmanAtEveryScale_of_discreteAllLarge C S hdepth D B,
    isKatzTaoAtEveryScale_of_discreteAllLarge C S hdepth D B⟩

/-! ## Sharp finite obstruction to parent-only interpolation -/

/-- Fine sources before the merge. -/
abbrev SplitSource (N : Nat) := Fin N

/-- At the lower scale every source has its own parent. -/
def identityLowerParent {N : Nat} : SplitSource N -> Fin N := id

/-- At the upper scale all sources have merged into one parent. -/
def collapsedUpperParent {N : Nat} : SplitSource N -> Unit := fun _ => ()

/-- The cross-scale parent map also merges every lower parent. -/
def collapsedCrossParent {N : Nat} : Fin N -> Unit := fun _ => ()

theorem collapsed_parent_compatible {N : Nat} (i : SplitSource N) :
    collapsedUpperParent i = collapsedCrossParent (identityLowerParent i) :=
  rfl

/-- Abstract fine fiber of a parent assignment. -/
def assignmentFiber {N P : Nat} (parent : Fin N -> Fin P) (k : Fin P) :
    Finset (Fin N) :=
  Finset.univ.filter fun i => parent i = k

theorem identityLowerFiber_card {N : Nat} (k : Fin N) :
    (assignmentFiber (identityLowerParent (N := N)) k).card = 1 := by
  change ((Finset.univ.filter fun i : Fin N => i = k).card) = 1
  rw [Finset.filter_eq', if_pos (Finset.mem_univ k), Finset.card_singleton]

/-- Version of the collapsed upper assignment with a one-element finite
parent type, used to expose exact fiber cardinality. -/
def collapsedUpperParentFin {N : Nat} : SplitSource N -> Fin 1 :=
  fun _ => 0

theorem collapsedUpperFiber_card (N : Nat) :
    (assignmentFiber (collapsedUpperParentFin (N := N)) (0 : Fin 1)).card = N := by
  simp [assignmentFiber, collapsedUpperParentFin]

/-- Parent composition and vacuous carrier containment permit an arbitrary
fiber-load jump: `N` singleton lower fibers may merge into one `N`-source
upper fiber.  Thus the reverse parent-concentration field above cannot be
removed or bounded by a universal constant from parent data alone. -/
theorem no_uniform_parent_only_fiber_load (L : Nat) :
    exists N : Nat, L < N ∧
      (forall k : Fin N,
        (assignmentFiber (identityLowerParent (N := N)) k).card = 1) ∧
      (assignmentFiber (collapsedUpperParentFin (N := N)) (0 : Fin 1)).card = N := by
  refine ⟨L + 1, Nat.lt_succ_self L, ?_, ?_⟩
  · exact identityLowerFiber_card
  · exact collapsedUpperFiber_card (L + 1)

#print axioms lower_fiber_subset_upper_fiber
#print axioms isFrostmanAtScale_of_upperEndpoint
#print axioms isKatzTaoAtScale_of_upperEndpoint
#print axioms isFrostmanAtEveryScale_of_discreteAllLarge
#print axioms isKatzTaoAtEveryScale_of_discreteAllLarge
#print axioms isStickyAtEveryScale_of_discreteAllLarge
#print axioms no_uniform_parent_only_fiber_load

end

end FamilyStickyScaleChainArbitraryRadiusBoundsV1

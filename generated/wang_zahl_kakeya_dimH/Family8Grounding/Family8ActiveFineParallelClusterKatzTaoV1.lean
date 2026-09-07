import Family8Grounding.Family8EpsilonExtremalSameScaleFineParallelClusterV1
import Family8Grounding.Family8EpsilonExtremalActiveStickyXUpperV1
import Family8Grounding.Family8FiniteRigidMotionDirectionTranslationSupportV1
import Family8Grounding.Family8FixedJohnAutomaticRepetitionUpperV1
import Family8Grounding.Family8SphereDirectionPackingV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1
import Family6FiniteMapFiberCapCardV1
import Mathlib.Tactic

/-!
# An honest directional-cluster Katz--Tao bridge

A uniform bound on the active fine directional clusters does not by itself
give the small-power Katz--Tao coefficient used by the long-core endpoint.
It does, however, give a genuine global bound after covering the unit sphere
by a finite direction net.  Each direction-net fibre lies in one literal
`activeFineParallelCluster`, so the active cardinality is bounded by the
number of net directions times the supplied cluster bound.  The general
cardinality Katz--Tao theorem then gives the same product as a valid
Katz--Tao coefficient for the active subtype datum.

No upper bound on `parallelLoss`, no `delta ^ (-eta)` absorption, and no
spatial-concentration hypothesis is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8ActiveFineParallelClusterKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8EpsilonExtremalActiveStickyXUpperV1
open Family8EpsilonExtremalSameScaleFineParallelClusterV1
open Family8FixedJohnAutomaticRepetitionUpperV1

noncomputable section

universe u

/-- The actual Euclidean unit sphere in the repository's three-space. -/
def activeFineDirectionSphere : Set Space := Metric.sphere (0 : Space) 1

theorem mem_activeFineDirectionSphere_iff_norm_eq_one (v : Space) :
    v ∈ activeFineDirectionSphere ↔ ‖v‖ = 1 := by
  simp [activeFineDirectionSphere]

/-- The net mesh is chosen so that its `2 * mesh` covering radius is exactly
the tube radius. -/
def activeFineDirectionMesh (delta : NNReal) : NNReal := delta / 2

theorem activeFineDirectionMesh_pos {delta : NNReal} (hdelta : 0 < delta) :
    0 < activeFineDirectionMesh delta := by
  exact div_pos hdelta (by norm_num)

/-- Total boundedness makes the local maximal direction packing finite. -/
theorem activeFineDirectionSphere_packingNumber_ne_top
    {delta : NNReal} (hdelta : 0 < delta) :
    Metric.packingNumber (2 * activeFineDirectionMesh delta)
      activeFineDirectionSphere ≠ ⊤ := by
  have htot : TotallyBounded activeFineDirectionSphere :=
    (isCompact_sphere (0 : Space) 1).totallyBounded
  obtain ⟨N, _hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := activeFineDirectionMesh delta)
      (activeFineDirectionMesh_pos hdelta).ne' htot
  have hext_lt_top :
      Metric.externalCoveringNumber (activeFineDirectionMesh delta)
          activeFineDirectionSphere < ⊤ :=
    hNcover.externalCoveringNumber_le_encard.trans_lt hNfinite.encard_lt_top
  exact
    ((Metric.packingNumber_two_mul_le_externalCoveringNumber
      (activeFineDirectionMesh delta) activeFineDirectionSphere).trans_lt
        hext_lt_top).ne

/-- A finite maximal separated net on the unit sphere, specialized to the
fine radius. -/
theorem exists_activeFineDirectionPackingCertificate
    {delta : NNReal} (hdelta : 0 < delta) :
    Nonempty
      (PackingCertificate activeFineDirectionSphere
        (activeFineDirectionMesh delta)) := by
  have hpack :
      Metric.packingNumber (2 * activeFineDirectionMesh delta)
          activeFineDirectionSphere ≠ ⊤ :=
    activeFineDirectionSphere_packingNumber_ne_top hdelta
  let S : Set Space :=
    Metric.maximalSeparatedSet (2 * activeFineDirectionMesh delta)
      activeFineDirectionSphere
  have hSfinite : S.Finite := by
    rw [← Set.encard_lt_top_iff]
    rw [show S.encard =
        Metric.packingNumber (2 * activeFineDirectionMesh delta)
          activeFineDirectionSphere by
      simpa [S] using Metric.encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨{
    centers := hSfinite.toFinset
    centers_subset := ?_
    separated := ?_
    cover := ?_ }⟩
  · simpa [S] using
      (Metric.maximalSeparatedSet_subset :
        Metric.maximalSeparatedSet (2 * activeFineDirectionMesh delta)
            activeFineDirectionSphere ⊆ activeFineDirectionSphere)
  · simpa [S] using
      (Metric.isSeparated_maximalSeparatedSet :
        Metric.IsSeparated (2 * activeFineDirectionMesh delta)
          (Metric.maximalSeparatedSet (2 * activeFineDirectionMesh delta)
            activeFineDirectionSphere : Set Space))
  · simpa [S] using Metric.isCover_maximalSeparatedSet hpack

noncomputable def activeFineDirectionPackingCertificate
    {delta : NNReal} (hdelta : 0 < delta) :
    PackingCertificate activeFineDirectionSphere
      (activeFineDirectionMesh delta) :=
  Classical.choice (exists_activeFineDirectionPackingCertificate hdelta)

abbrev ActiveFineDirectionChoice (delta : NNReal) (hdelta : 0 < delta) :=
  ↥(activeFineDirectionPackingCertificate hdelta).centers

@[simp] theorem activeFineDirectionChoice_norm
    {delta : NNReal} (hdelta : 0 < delta)
    (g : ActiveFineDirectionChoice delta hdelta) :
    ‖(g.1 : Space)‖ = 1 := by
  apply (mem_activeFineDirectionSphere_iff_norm_eq_one g.1).mp
  exact (activeFineDirectionPackingCertificate hdelta).centers_subset g.2

theorem activeFineDirectionChoice_cover
    {delta : NNReal} (hdelta : 0 < delta)
    (v : Space) (hv : ‖v‖ = 1) :
    ∃ g : ActiveFineDirectionChoice delta hdelta,
      edist v (g.1 : Space) ≤ (2 * activeFineDirectionMesh delta : NNReal) := by
  have hvSphere : v ∈ activeFineDirectionSphere :=
    (mem_activeFineDirectionSphere_iff_norm_eq_one v).2 hv
  obtain ⟨g, hg, hvg⟩ :=
    (activeFineDirectionPackingCertificate hdelta).cover hvSphere
  exact ⟨⟨g, hg⟩, hvg⟩

/-- The literal finite geometric loss in the direction-net decomposition. -/
def activeFineDirectionGeometricLoss (delta : NNReal) (hdelta : 0 < delta) : Nat :=
  Fintype.card (ActiveFineDirectionChoice delta hdelta)

/-- A tube whose axis has exactly a prescribed unit direction.  Its location
is irrelevant because `EssentiallyParallelAtScale` sees only directions. -/
def directionCenterTube (delta : NNReal) (v : Space) (hv : ‖v‖ = 1) : Tube delta where
  axis := {
    base := 0
    direction := v
    norm_direction := hv }

@[simp] theorem directionCenterTube_direction
    (delta : NNReal) (v : Space) (hv : ‖v‖ = 1) :
    (directionCenterTube delta v hv).axis.direction = v := rfl

/-- For unit vectors, projective sine-angle is bounded by ordinary Euclidean
distance.  This deliberately keeps both orientations: near-antipodal vectors
also have small projective angle, while the stated upper bound remains true. -/
theorem sin_angle_le_dist_of_norm_eq_one
    (v w : Space) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    Real.sin (InnerProductGeometry.angle v w) ≤ dist v w := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    norm_num at hv
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    norm_num at hw
  let c : Real := ⟪v, w⟫_Real
  have hcabs : |c| ≤ 1 := by
    dsimp only [c]
    simpa only [hv, hw, one_mul] using abs_real_inner_le_norm v w
  have hcUpper : c ≤ 1 := le_trans (le_abs_self c) hcabs
  have hcLower : -1 ≤ c := neg_le_of_abs_le hcabs
  have hrad : 0 ≤ 1 - c * c := by
    have hleft : 0 ≤ 1 - c := sub_nonneg.mpr hcUpper
    have hright : 0 ≤ 1 + c := by linarith
    nlinarith [mul_nonneg hleft hright]
  have hsin :
      Real.sin (InnerProductGeometry.angle v w) = Real.sqrt (1 - c * c) := by
    have h := InnerProductGeometry.sin_angle hv0 hw0
    rw [hv, hw] at h
    simp only [one_mul, div_one] at h
    have hvv : ⟪v, v⟫_Real = 1 := by
      rw [real_inner_self_eq_norm_sq, hv]
      norm_num
    have hww : ⟪w, w⟫_Real = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]
      norm_num
    rw [hvv, hww] at h
    simpa only [c, one_mul] using h
  have hdistSq : (dist v w) ^ 2 = 2 - 2 * c := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    have hvv : ⟪v, v⟫_Real = 1 := by
      rw [real_inner_self_eq_norm_sq, hv]
      norm_num
    have hww : ⟪w, w⟫_Real = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]
      norm_num
    rw [hvv, hww]
    have hwv : ⟪w, v⟫_Real = c := by
      dsimp only [c]
      exact (real_inner_comm w v).symm
    rw [hwv]
    ring
  have hradLe : 1 - c * c ≤ (dist v w) ^ 2 := by
    rw [hdistSq]
    nlinarith [sq_nonneg (1 - c)]
  rw [hsin]
  have hsqrtSq : (Real.sqrt (1 - c * c)) ^ 2 = 1 - c * c :=
    Real.sq_sqrt hrad
  nlinarith [Real.sqrt_nonneg (1 - c * c), (dist_nonneg : 0 ≤ dist v w)]

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

/-- Assign each active tube to a covering unit-sphere direction. -/
noncomputable def activeFineDirectionChoiceOf
    (hdelta : 0 < delta) (i : {i // i ∈ active}) :
    ActiveFineDirectionChoice delta hdelta :=
  Classical.choose
    (activeFineDirectionChoice_cover hdelta
      (fine.tubes i.1).axis.direction
      (fine.tubes i.1).axis.norm_direction)

/-- The assigned net direction is within the tube scale in ordinary
Euclidean distance. -/
theorem activeFineDirectionChoiceOf_dist_le
    (hdelta : 0 < delta) (i : {i // i ∈ active}) :
    dist (fine.tubes i.1).axis.direction
      ((activeFineDirectionChoiceOf (fine := fine) hdelta i).1 : Space) ≤
        (delta : Real) := by
  have hcover := Classical.choose_spec
    (activeFineDirectionChoice_cover hdelta
      (fine.tubes i.1).axis.direction
      (fine.tubes i.1).axis.norm_direction)
  have hfinite :
      ((2 * activeFineDirectionMesh delta : NNReal) : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hcoverReal := ENNReal.toReal_mono hfinite hcover
  have hdist :
      dist (fine.tubes i.1).axis.direction
          ((activeFineDirectionChoiceOf (fine := fine) hdelta i).1 : Space) ≤
        ((2 * activeFineDirectionMesh delta : NNReal) : Real) := by
    have hrhs :
        (((2 * activeFineDirectionMesh delta : NNReal) : ENNReal)).toReal =
          ((2 * activeFineDirectionMesh delta : NNReal) : Real) := rfl
    rw [← dist_edist, hrhs] at hcoverReal
    exact hcoverReal
  simpa only [activeFineDirectionMesh, mul_div_cancel₀ _
    (by norm_num : (2 : NNReal) ≠ 0)] using hdist

/-- Every assignment fibre is contained in the literal active fine parallel
cluster centred at the corresponding net direction. -/
theorem activeFineDirectionChoiceOf_fiber_subset_parallelCluster
    (hdelta : 0 < delta) (g : ActiveFineDirectionChoice delta hdelta) :
    (Finset.univ.filter fun i : {i // i ∈ active} =>
        activeFineDirectionChoiceOf (fine := fine) hdelta i = g).image
          (fun i => i.1) ⊆
      activeFineParallelCluster fine active
        (directionCenterTube delta (g.1 : Space)
          (activeFineDirectionChoice_norm hdelta g)) := by
  classical
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hjEq := (Finset.mem_filter.mp hj).2
  apply (mem_activeFineParallelCluster fine active _ j.1).2
  refine ⟨j.2, ?_⟩
  unfold EssentiallyParallelAtScale
  have hdist := activeFineDirectionChoiceOf_dist_le
    (fine := fine) hdelta j
  have hsin := sin_angle_le_dist_of_norm_eq_one
    (fine.tubes j.1).axis.direction
    ((activeFineDirectionChoiceOf (fine := fine) hdelta j).1 : Space)
    (fine.tubes j.1).axis.norm_direction
    (activeFineDirectionChoice_norm hdelta
      (activeFineDirectionChoiceOf (fine := fine) hdelta j))
  simpa only [directionCenterTube_direction, hjEq] using hsin.trans hdist

/-- A uniform active directional-cluster cap bounds the whole active set by
the finite sphere-net loss times that cap. -/
theorem active_card_le_directionGeometricLoss_mul
    (hdelta : 0 < delta) {L : Nat}
    (hcluster : ∀ U : Tube delta,
      (activeFineParallelCluster fine active U).card ≤ L) :
    active.card ≤ activeFineDirectionGeometricLoss delta hdelta * L := by
  classical
  let Parameter := {i // i ∈ active}
  let Choice := ActiveFineDirectionChoice delta hdelta
  let code : Parameter → Choice :=
    activeFineDirectionChoiceOf (fine := fine) hdelta
  have hfiber : ∀ g ∈ (Finset.univ : Finset Choice),
      ((Finset.univ : Finset Parameter).filter fun i => code i = g).card ≤ L := by
    intro g _hg
    have himageCard :
        (((Finset.univ : Finset Parameter).filter fun i => code i = g).image
          (fun i => i.1)).card =
        ((Finset.univ : Finset Parameter).filter fun i => code i = g).card := by
      apply Finset.card_image_iff.mpr
      intro i _hi j _hj hij
      exact Subtype.ext hij
    have hsubset :
        (((Finset.univ : Finset Parameter).filter fun i => code i = g).image
          (fun i => i.1)) ⊆
        activeFineParallelCluster fine active
          (directionCenterTube delta (g.1 : Space)
            (activeFineDirectionChoice_norm hdelta g)) := by
      simpa only [Parameter, Choice, code] using
        activeFineDirectionChoiceOf_fiber_subset_parallelCluster
          (fine := fine) (active := active) hdelta g
    rw [← himageCard]
    exact (Finset.card_le_card hsubset).trans
      (hcluster (directionCenterTube delta (g.1 : Space)
        (activeFineDirectionChoice_norm hdelta g)))
  have hcard := Family6FiniteMapFiberCapCardV1.card_le_fiberCap_mul_card
    (Finset.univ : Finset Parameter) (Finset.univ : Finset Choice)
    code L (by simp) hfiber
  change active.card ≤ activeFineDirectionGeometricLoss delta hdelta * L
  simpa only [Parameter, Choice, Fintype.card_coe, Finset.card_univ,
    activeFineDirectionGeometricLoss, Nat.mul_comm] using hcard

/-- The cardinality bound is already a global Katz--Tao bound for the active
subtype family. -/
theorem isKatzTao_activeSubtype_of_activeFineParallelCluster_bound
    {Y : Shading fine.bodyFamily} (hdelta : 0 < delta) {L : Nat}
    (hcluster : ∀ U : Tube delta,
      (activeFineParallelCluster fine active U).card ≤ L) :
    IsKatzTao
      ((activeFineDirectionGeometricLoss delta hdelta : ENNReal) * (L : ENNReal))
      (activeSubtypeDatum fine Y active).family.bodyFamily := by
  have hbase := isKatzTao_cardinality
    (activeSubtypeDatum fine Y active).family.bodyFamily
  apply hbase.mono
  have hcardNat : Fintype.card {i // i ∈ active} ≤
      activeFineDirectionGeometricLoss delta hdelta * L := by
    simpa only [Fintype.card_coe] using
      (active_card_le_directionGeometricLoss_mul
        (fine := fine) (active := active) hdelta hcluster)
  exact_mod_cast hcardNat

/-- Epsilon-extremality supplies the positive radius needed by the net.  The
cluster cap remains an explicit honest input; in particular this theorem does
not manufacture an upper bound for `parallelLoss`. -/
theorem isKatzTao_activeSubtype_of_epsilonExtremal_clusterBound
    {Y : Shading fine.bodyFamily} {parallelLoss : Nat}
    {epsilon sigma : Real}
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma)
    {L : Nat}
    (hcluster : ∀ U : Tube delta,
      (activeFineParallelCluster fine active U).card ≤ L) :
    IsKatzTao
      ((activeFineDirectionGeometricLoss delta G.delta_pos : ENNReal) *
        (L : ENNReal))
      (activeSubtypeDatum fine Y active).family.bodyFamily :=
  isKatzTao_activeSubtype_of_activeFineParallelCluster_bound
    G.delta_pos hcluster

#print axioms sin_angle_le_dist_of_norm_eq_one
#print axioms activeFineDirectionChoiceOf_dist_le
#print axioms active_card_le_directionGeometricLoss_mul
#print axioms isKatzTao_activeSubtype_of_activeFineParallelCluster_bound
#print axioms isKatzTao_activeSubtype_of_epsilonExtremal_clusterBound

end
end Family8ActiveFineParallelClusterKatzTaoV1

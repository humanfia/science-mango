import «Family4SevenItemsMaster»
import Submission.Kakeya.ConvexFactoring.FiberCoveringGrowthFromMultiplicity
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Family4GlobalExtremalUpstream

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FrozenNeighborhoodAssembly
open Family4FrozenDensityAdapter
open Family4ExtremalConstruction
open Family4SevenItemsMaster
open Family4LambdaUniform

noncomputable section

set_option linter.unusedSectionVars false

/-- WZ's “essentially distinct” condition: two tubes overlap in at most half
the larger tube volume.  This is Definition 2.1(a) in its indexed form. -/
def EssentiallyDistinct {δ : NNReal} (T U : Tube δ) : Prop :=
  volume (T.carrier ∩ U.carrier) ≤
    (2 : ℝ≥0∞)⁻¹ * max (volume T.carrier) (volume U.carrier)

/-- “Essentially parallel at scale `tau`” is expressed by the unoriented
sine-angle of the two tube axes.  The sine makes the relation insensitive to
reversing one parametrized axis. -/
def EssentiallyParallelAtScale {τ : NNReal} (T U : Tube τ) : Prop :=
  Real.sin (InnerProductGeometry.angle T.axis.direction U.axis.direction) ≤ τ

/-- A finite supplied `tau`-tube cover of an active `delta`-family.  This is
the data quantified over in WZ Definition 2.1(b); no existence theorem is
built into the structure. -/
structure TubeScaleCover {δ τ : NNReal} {ι : Type*} [DecidableEq ι]
    (fineFamily : UniformTubeFamily δ ι) (active : Finset ι) where
  count : ℕ
  tubes : Fin count → Tube τ
  parent : ι → Fin count
  carrier_subset : ∀ i ∈ active,
    (fineFamily.tubes i).carrier ⊆ (tubes (parent i)).carrier

namespace TubeScaleCover

noncomputable def parallelCluster {δ τ : NNReal} {ι : Type*} [DecidableEq ι]
    {fineFamily : UniformTubeFamily δ ι} {active : Finset ι}
    (C : @TubeScaleCover δ τ ι _ fineFamily active)
    (U : Tube τ) : Finset (Fin C.count) := by
  classical
  exact Finset.univ.filter fun q => EssentiallyParallelAtScale (C.tubes q) U

end TubeScaleCover

/-- Direct formalization of the defining (not self-similarity) hypotheses of
a WZ epsilon-extremal family at one scale.

The real powers are the paper's `delta^epsilon` mass lower bound and
`delta^(sigma-epsilon)` union-volume upper bound.  `parallelLoss` is the
integer-rounded version of `delta^(-epsilon)`.  The active carriers are placed
in the unit ball, matching the standing boundedness convention in WZ.

Crucially, there is no field asserting that a rescaled fiber is extremal and
no pointwise multiplicity conclusion.  Those are Proposition 2.7 outputs. -/
structure EpsilonExtremalTubeFamily
    {δ : NNReal} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : UniformTubeFamily δ ι) (Y : Shading family.bodyFamily)
    (active : Finset ι) (parallelLoss : ℕ)
    (epsilon sigma : ℝ) : Prop where
  delta_pos : 0 < δ
  delta_le_half : δ ≤ (2 : NNReal)⁻¹
  epsilon_pos : 0 < epsilon
  active_nonempty : active.Nonempty
  support : ∀ i ∉ active, Y.carrier i = ∅
  contained_in_unit_ball : ∀ i ∈ active,
    (family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1
  essentially_distinct : Set.Pairwise (↑active : Set ι) fun i j =>
    EssentiallyDistinct (family.tubes i) (family.tubes j)
  parallelLoss_rounds_power :
    (δ : ℝ≥0∞) ^ (-epsilon) ≤ (parallelLoss : ℝ≥0∞)
  scale_covers : ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
    ∃ C : @TubeScaleCover δ τ ι _ family active,
      ∀ U : Tube τ, (C.parallelCluster U).card ≤ parallelLoss
  shading_mass_lower :
    (δ : ℝ≥0∞) ^ epsilon ≤ Y.shadingMass
  union_volume_upper :
    volume Y.shadedUnion ≤ (δ : ℝ≥0∞) ^ (sigma - epsilon)

namespace EpsilonExtremalTubeFamily

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}
  {P : CoarseTubePartition fineFamily coarseFamily}
  {Y : Shading fineFamily.bodyFamily}
  {active : Finset ι} {parallelLoss : ℕ}
  {epsilon sigma : ℝ}

/-- The active support identity converts the paper's global shading-mass
lower bound into the formal active restriction used by the assembly. -/
theorem restrictTo_active_mass_eq
    (G : EpsilonExtremalTubeFamily fineFamily Y active parallelLoss epsilon sigma)
    (hactive : active = P.fineIndices) :
    (IndexedShadingRefinement.restrictTo Y
      P.asConvexFactorization.index.fine).shading.shadingMass =
      Y.shadingMass := by
  classical
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hiActive
  change i ∉ P.index.fine at hiActive
  have hiG : i ∉ active := by
    simpa [hactive, CoarseTubePartition.fineIndices] using hiActive
  rw [G.support i hiG]
  simp

/-- The defining mass lower bound and the standard tube-volume upper bound
already imply the lower cardinality half quoted after WZ Definition 2.6.
No essential-distinct packing theorem is needed for this direction. -/
theorem cardinality_lower_crossMultiplied
    (G : EpsilonExtremalTubeFamily fineFamily Y active parallelLoss epsilon sigma) :
    (delta : ℝ≥0∞) ^ epsilon ≤
      (active.card : ℝ≥0∞) * (8 * (delta : ℝ≥0∞) ^ 2) := by
  calc
    (delta : ℝ≥0∞) ^ epsilon ≤ Y.shadingMass := G.shading_mass_lower
    _ = ∑ i ∈ active, volume (Y.carrier i) := by
      unfold Shading.shadingMass
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _hi hi
      rw [G.support i hi]
      simp
    _ ≤ ∑ _i ∈ active, 8 * (delta : ℝ≥0∞) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (measure_mono (Y.carrier_subset i)).trans
        ((fineFamily.tubes i).volume_le_eight_mul_sq_of_le_half
          G.delta_le_half)
    _ = (active.card : ℝ≥0∞) *
        (8 * (delta : ℝ≥0∞) ^ 2) := by simp

/-- Positive global extremal mass survives the actual frozen assembly, so its
final fine shading contains a point.  This supplies the witness needed to
connect a nonzero dyadic multiplicity bucket to a pointwise WZ bound. -/
theorem exists_finalFine_witness {r : ℝ}
    (G : EpsilonExtremalTubeFamily fineFamily Y active parallelLoss epsilon sigma)
    (hactive : active = P.fineIndices)
    (A : Assembly P.asConvexFactorization Y r) :
    ∃ i x, x ∈ A.refinement.shading.carrier i := by
  have hpow : 0 < (delta : ℝ≥0∞) ^ epsilon := by
    exact ENNReal.rpow_pos (ENNReal.coe_pos.mpr G.delta_pos) (by simp)
  have hsource : 0 < Y.shadingMass :=
    hpow.trans_le G.shading_mass_lower
  have hrestricted : 0 <
      (IndexedShadingRefinement.restrictTo Y
        P.asConvexFactorization.index.fine).shading.shadingMass := by
    rw [G.restrictTo_active_mass_eq hactive]
    exact hsource
  have hfinal : 0 < A.refinement.shading.shadingMass := by
    by_contra hnot
    have hz : A.refinement.shading.shadingMass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hret := A.retained
    unfold WithinFactor at hret
    rw [hz, nsmul_zero] at hret
    exact (not_le_of_gt hrestricted) hret
  unfold Shading.shadingMass at hfinal
  rw [Finset.sum_pos_iff] at hfinal
  obtain ⟨i, _hi, hvol⟩ := hfinal
  have hne : (A.refinement.shading.carrier i).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hvol
    simp at hvol
  obtain ⟨x, hx⟩ := hne
  exact ⟨i, x, hx⟩

/-- Minimal special-case interface for the genuinely new WZ multiscale
self-similarity theorem.

Everything except `hfiberCardinality` is derived from current APIs and the
global epsilon-extremal definition:

* nonempty final-fine witness: global mass + assembly retention;
* pointwise fiber bound: multiplicity <= fiber cardinality <=
  `branchingLoss * branching`;
* parent activity: the assembly index support and the supplied partition.

`hfiberCardinality` is precisely the division-free cardinality conclusion of
unit-rescaling each WZ fiber.  Proving it from global extremality is the new
content of WZ Proposition 2.7 and is intentionally a theorem hypothesis here,
not a field of `EpsilonExtremalTubeFamily`. -/
theorem toExtremalTubeFamily_of_multiscaleCardinality {r : ℝ}
    (G : EpsilonExtremalTubeFamily fineFamily Y active parallelLoss epsilon sigma)
    (hactive : active = P.fineIndices)
    (A : Assembly P.asConvexFactorization Y r)
    (coveringLoss : ℝ≥0∞)
    (hfiberCardinality : ∀ k ∈ P.coarseIndices,
      (rho : ℝ≥0∞) ^ 2 ≤ coveringLoss *
        ((P.asConvexFactorization.index.fiber k).card : ℝ≥0∞) *
          (delta : ℝ≥0∞) ^ 2) :
    Nonempty (ExtremalTubeFamily A) := by
  obtain ⟨i, x, hxi⟩ := G.exists_finalFine_witness hactive A
  have hiIndices : i ∈ A.refinement.indices := by
    by_contra hi
    rw [A.refinement.carrier_eq_empty_of_not_mem i hi] at hxi
    exact hxi
  have hiFine : i ∈ P.asConvexFactorization.index.fine :=
    A.indices_subset_fine hiIndices
  let k := P.asConvexFactorization.index.parent i
  have hkConvex : k ∈ P.asConvexFactorization.index.coarse :=
    P.asConvexFactorization.index.parent_mem i hiFine
  have hk : k ∈ P.coarseIndices := by
    change k ∈ P.index.coarse at hkConvex
    simpa only [CoarseTubePartition.coarseIndices] using hkConvex
  have hiFiber : i ∈ P.asConvexFactorization.index.fiber k :=
    (P.asConvexFactorization.index.mem_fiber i k).2 ⟨hiFine, rfl⟩
  refine ⟨{
    multiplicityScale := P.branchingLoss * P.branching
    coveringLoss := coveringLoss
    parent := k
    parent_mem := hk
    witness := x
    witness_mem := Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hxi⟩
    pointwise_fiber_le := ?_
    normalized_covering := hfiberCardinality k hk }⟩
  intro l hl y _hy
  calc
    P.asConvexFactorization.fiberMultiplicity A.refinement.shading l y ≤
        (P.asConvexFactorization.index.fiber l).card :=
      FiberwiseMultiplicityAssembly.fiberMultiplicity_le_fiber_card P.asConvexFactorization
        A.refinement.shading l y
    _ ≤ P.branchingLoss * P.branching :=
      P.fiber_card_le_loss_mul_branching l hl

end EpsilonExtremalTubeFamily
end
end Family4GlobalExtremalUpstream

#print axioms Family4GlobalExtremalUpstream.EpsilonExtremalTubeFamily.cardinality_lower_crossMultiplied
#print axioms Family4GlobalExtremalUpstream.EpsilonExtremalTubeFamily.exists_finalFine_witness
#print axioms Family4GlobalExtremalUpstream.EpsilonExtremalTubeFamily.toExtremalTubeFamily_of_multiscaleCardinality

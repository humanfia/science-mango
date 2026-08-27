import ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit
import ArchonPhysics.RepeatedParentChildMismatchQuadraticBound

/-!
# Repeated parent--child mismatch weak limits have no zero atom

The predicate-restricted finite-volume mismatch measures are bundled as
finite measures and normalized per site.  The frozen iid quadratic estimates
then apply literally to these bundled objects.  Consequently, every supplied
finite-measure weak limit of either repeated parent--child sector gives zero
mass to exact resonance.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull

open ArchonPhysics
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchQuadraticBound
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- Every predicate-restricted positive weighted mismatch measure is finite. -/
theorem positiveWeightedMismatchMeasureWhere_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) :
    IsFiniteMeasure (positiveWeightedMismatchMeasureWhere m sign keep) := by
  constructor
  unfold positiveWeightedMismatchMeasureWhere
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hkeep : IsPositiveOrderedTriple m modes ∧ keep modes
  · simp [hkeep]
  · simp [hkeep]

/-- Predicate-restricted mismatch measure as a bundled finite measure. -/
def positiveWeightedMismatchFiniteMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) : FiniteMeasure Real :=
  ⟨positiveWeightedMismatchMeasureWhere m sign keep,
    positiveWeightedMismatchMeasureWhere_isFinite m sign keep⟩

/-- Predicate-restricted mismatch measure with the physical per-site
normalization. -/
def perSitePositiveWeightedMismatchFiniteMeasureWhere
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) : FiniteMeasure Real :=
  ((N : NNReal)⁻¹) •
    positiveWeightedMismatchFiniteMeasureWhere m sign keep

/-- Exact evaluation formula for the per-site restricted measure. -/
theorem perSitePositiveWeightedMismatchFiniteMeasureWhere_apply_toReal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (keep : OrderedModeTriple N → Prop) (s : Set Real) :
    (((perSitePositiveWeightedMismatchFiniteMeasureWhere
        m sign keep : FiniteMeasure Real) : Measure Real) s).toReal =
      (positiveWeightedMismatchMeasureWhere m sign keep s).toReal /
        (N : Real) := by
  unfold perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply,
    ENNReal.toReal_smul]
  simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  rw [div_eq_inv_mul]
  unfold positiveWeightedMismatchFiniteMeasureWhere
  rfl

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Frozen-iid per-site mismatch finite measure for the first disjoint
parent--child sector, indexed by volume `n + 1`. -/
def iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) : FiniteMeasure Real :=
  perSitePositiveWeightedMismatchFiniteMeasureWhere
    (ensemble.restrictPositiveMass (N := n + 1) omega)
    decayInteractionSign ParentChildOneRepeated

/-- Frozen-iid per-site mismatch finite measure for the second disjoint
parent--child sector. -/
def iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) : FiniteMeasure Real :=
  perSitePositiveWeightedMismatchFiniteMeasureWhere
    (ensemble.restrictPositiveMass (N := n + 1) omega)
    decayInteractionSign ParentChildTwoRepeated

theorem iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_smallBall
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (((iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega n : FiniteMeasure Real) : Measure Real)
        (absoluteMismatchSublevel delta)).toReal ≤
      (5 / 8 : Real) * delta ^ 2 := by
  rw [iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure,
    perSitePositiveWeightedMismatchFiniteMeasureWhere_apply_toReal]
  exact iid_parentChildOneRepeated_mismatchMeasure_toReal_div_volume_le_sq
    ensemble omega hdelta hdelta1

theorem iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_smallBall
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) {delta : Real} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    (((iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega n : FiniteMeasure Real) : Measure Real)
        (absoluteMismatchSublevel delta)).toReal ≤
      (5 / 8 : Real) * delta ^ 2 := by
  rw [iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure,
    perSitePositiveWeightedMismatchFiniteMeasureWhere_apply_toReal]
  exact iid_parentChildTwoRepeated_mismatchMeasure_toReal_div_volume_le_sq
    ensemble omega hdelta hdelta1

/-- Every finite-measure weak limit of the first repeated parent--child
sector is exact-resonance-null. -/
theorem iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_weakLimit_zeroAtom
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
      atTop (nhds target)) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  apply finiteMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
    target hlimit (5 / 8 : Real) (by norm_num)
  intro n delta hdelta hdelta1
  exact iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure_smallBall
    ensemble omega n hdelta hdelta1

/-- Every finite-measure weak limit of the second repeated parent--child
sector is exact-resonance-null. -/
theorem iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_weakLimit_zeroAtom
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
      atTop (nhds target)) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  apply finiteMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure ensemble omega)
    target hlimit (5 / 8 : Real) (by norm_num)
  intro n delta hdelta hdelta1
  exact iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure_smallBall
    ensemble omega n hdelta hdelta1

end

end ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull

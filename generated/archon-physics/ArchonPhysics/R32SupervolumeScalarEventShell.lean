import ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2
import ArchonPhysics.R32DiluteBootstrapClosureCompleteV3

/-!
# Scalar and event shell for the R32 supervolume persistence argument

This file contains only the final real-analysis and measure-theoretic shell.
For the explicit supervolume coupling `g_j = 1 / (j + 1)`, it records the
vanishing cubic Duhamel error and the resulting quadratic modal-energy error.
It also packages the exact eventual normalization margin needed below the
frozen `1 / 8` separation.

No trajectory estimate, collision expansion, or kinetic assumption occurs
here.  The generic event lemma permits the pathwise Hamiltonian comparison to
hold almost everywhere on the measurable free-concentration event; no
measurability of that auxiliary almost-sure realization event is required.
-/

namespace ArchonPhysics.R32SupervolumeScalarEventShell

open ArchonPhysics
open ArchonPhysics.R32DiluteBootstrapClosureCompleteV3
open ArchonPhysics.R32SupervolumeJointLimit
open ArchonPhysics.R32SupervolumeMicroscopicPersistenceV2
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- The `O(g^3)` canonical error along the explicit supervolume coupling. -/
def cubicError (B : Real) (j : Nat) : Real :=
  B * inverseLinearCoupling j ^ 3

/-- The sharp quadratic modal-energy `L1` error obtained from modal distance
`e` and the free phase-space norm `sqrt 2`. -/
def modalRawError (B : Real) (j : Nat) : Real :=
  (1 / 2 : Real) * cubicError B j *
    (cubicError B j + 2 * Real.sqrt 2)

/-- The normalization loss in the variable-error V4 late-window bound. -/
def normalizationLoss (B : Real) (j : Nat) : Real :=
  2 * modalRawError B j / (1 - modalRawError B j)

/-- Half of the strict gap between the frozen `1 / 8` separation and the
proposed hitting threshold. -/
def frozenHalfGap (delta : Real) : Real :=
  ((1 : Real) / 8 - delta) / 2

theorem inverseLinearCoupling_tendsto_zero_real :
    Tendsto inverseLinearCoupling atTop (nhds 0) :=
  (tendsto_nhdsWithin_iff.mp inverseLinearCoupling_tendsto_zero).1

/-- The explicit inverse-linear coupling eventually lies below the V3
bootstrap threshold.  A downstream assumption `1 <= C` is more than enough
for the nonnegativity hypothesis on `C` used here. -/
theorem eventually_inverseLinearCoupling_le_couplingThreshold
    {K C T : Real} (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T) :
    ∀ᶠ j in atTop,
      inverseLinearCoupling j <= couplingThreshold K C T := by
  have hthreshold : 0 < couplingThreshold K C T :=
    couplingThreshold_pos hK hC hT
  filter_upwards
    [inverseLinearCoupling_tendsto_zero_real.eventually
      (Iio_mem_nhds hthreshold)] with j hj
  exact hj.le

/-- The fixed kinetic constant is nonnegative and gives exactly the cubic
error scale used by the supervolume scalar shell. -/
theorem kineticConstant_nonneg_and_cubicError_eq
    {K C T : Real} (hK : 0 <= K) (hC : 0 <= C) (hT : 0 <= T) :
    0 <= kineticConstant K C T ∧
      ∀ j, cubicError (kineticConstant K C T) j =
        kineticConstant K C T * inverseLinearCoupling j ^ 3 := by
  refine ⟨(kineticConstant_pos hK hC hT).le, ?_⟩
  intro j
  rfl

theorem cubicError_tendsto_zero (B : Real) :
    Tendsto (cubicError B) atTop (nhds 0) := by
  have hg3 : Tendsto (fun j => inverseLinearCoupling j ^ 3)
      atTop (nhds (0 ^ 3)) :=
    inverseLinearCoupling_tendsto_zero_real.pow 3
  have hmul : Tendsto (fun j => B * inverseLinearCoupling j ^ 3)
      atTop (nhds (B * 0 ^ 3)) :=
    tendsto_const_nhds.mul hg3
  change Tendsto (fun j => B * inverseLinearCoupling j ^ 3)
    atTop (nhds 0)
  simpa using hmul

theorem modalRawError_tendsto_zero (B : Real) :
    Tendsto (modalRawError B) atTop (nhds 0) := by
  have he := cubicError_tendsto_zero B
  have hleft : Tendsto (fun j => (1 / 2 : Real) * cubicError B j)
      atTop (nhds ((1 / 2 : Real) * 0)) :=
    tendsto_const_nhds.mul he
  have hright : Tendsto
      (fun j => cubicError B j + 2 * Real.sqrt 2)
      atTop (nhds (0 + 2 * Real.sqrt 2)) :=
    he.add tendsto_const_nhds
  have hproduct := hleft.mul hright
  change Tendsto
    (fun j => (1 / 2 : Real) * cubicError B j *
      (cubicError B j + 2 * Real.sqrt 2)) atTop (nhds 0)
  simpa using hproduct

theorem normalizationLoss_tendsto_zero (B : Real) :
    Tendsto (normalizationLoss B) atTop (nhds 0) := by
  have hrho := modalRawError_tendsto_zero B
  have hnum : Tendsto (fun j => 2 * modalRawError B j)
      atTop (nhds (2 * 0)) :=
    tendsto_const_nhds.mul hrho
  have hden : Tendsto (fun j => 1 - modalRawError B j)
      atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hrho
  have hquot := hnum.div hden (by norm_num : (1 : Real) - 0 ≠ 0)
  have hlossFunction : normalizationLoss B =
      (fun j => 2 * modalRawError B j) /
        (fun j => 1 - modalRawError B j) := by
    funext j
    rfl
  rw [hlossFunction]
  simpa using hquot

theorem cubicError_nonneg {B : Real} (hB : 0 <= B) (j : Nat) :
    0 <= cubicError B j := by
  exact mul_nonneg hB (pow_nonneg (inverseLinearCoupling_pos j).le 3)

theorem modalRawError_nonneg {B : Real} (hB : 0 <= B) (j : Nat) :
    0 <= modalRawError B j := by
  unfold modalRawError
  have he := cubicError_nonneg hB j
  positivity

theorem frozenHalfGap_pos {delta : Real} (hdelta : delta < (1 : Real) / 8) :
    0 < frozenHalfGap delta := by
  unfold frozenHalfGap
  linarith

/-- Along the explicit supervolume coupling, the raw modal error is
eventually below one and its complete normalization loss is eventually no
larger than half of any fixed strict frozen-threshold gap. -/
theorem eventually_modalRawError_lt_one_and_normalizationLoss_le_frozenHalfGap
    (B : Real) {delta : Real} (hdelta : delta < (1 : Real) / 8) :
    ∀ᶠ j in atTop,
      modalRawError B j < 1 ∧
        normalizationLoss B j <= frozenHalfGap delta := by
  have hrho : ∀ᶠ j in atTop, modalRawError B j < 1 :=
    (modalRawError_tendsto_zero B).eventually
      (Iio_mem_nhds (by norm_num : (0 : Real) < 1))
  have hloss : ∀ᶠ j in atTop,
      normalizationLoss B j < frozenHalfGap delta :=
    (normalizationLoss_tendsto_zero B).eventually
      (Iio_mem_nhds (frozenHalfGap_pos hdelta))
  filter_upwards [hrho, hloss] with j hjrho hjloss
  exact ⟨hjrho, hjloss.le⟩

/-- If a measurable good event has vanishing real complement measure, and
almost every point of that event belongs to a target event, then the target
event has probability tending to one.  The target event itself need not be
declared measurable. -/
theorem tendsto_measure_one_of_measureReal_compl_tendsto_zero_of_ae_subset
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (goodEvent targetEvent : Nat -> Set Omega)
    (hgoodMeasurable : forall j, MeasurableSet (goodEvent j))
    (hcomplZero : Tendsto
      (fun j => probability.real (goodEvent j)ᶜ) atTop (nhds 0))
    (hsubset : forall j,
      ∀ᵐ x ∂probability, x ∈ goodEvent j -> x ∈ targetEvent j) :
    Tendsto (fun j => probability (targetEvent j)) atTop (nhds 1) := by
  have hgoodOne : Tendsto (fun j => probability (goodEvent j))
      atTop (nhds 1) :=
    tendsto_measure_one_of_measureReal_compl_le_budget
      probability goodEvent
      (fun j => probability.real (goodEvent j)ᶜ)
      hgoodMeasurable (fun _j => le_rfl) hcomplZero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hgoodOne
    (tendsto_const_nhds :
      Tendsto (fun _j : Nat => (1 : ENNReal)) atTop (nhds 1)) ?_ ?_
  · exact Filter.Eventually.of_forall fun j => measure_mono_ae (hsubset j)
  · exact Filter.Eventually.of_forall fun j => by
      calc
        probability (targetEvent j) <= probability (Set.univ : Set Omega) :=
          measure_mono (subset_univ _)
        _ = 1 := measure_univ

#print axioms cubicError_tendsto_zero
#print axioms modalRawError_tendsto_zero
#print axioms normalizationLoss_tendsto_zero
#print axioms eventually_inverseLinearCoupling_le_couplingThreshold
#print axioms kineticConstant_nonneg_and_cubicError_eq
#print axioms eventually_modalRawError_lt_one_and_normalizationLoss_le_frozenHalfGap
#print axioms tendsto_measure_one_of_measureReal_compl_tendsto_zero_of_ae_subset

end

end ArchonPhysics.R32SupervolumeScalarEventShell

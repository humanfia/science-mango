import ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily

/-!
# Hölder small balls for the three-site ordinary outer-history family

The explicit cubic estimate for the concrete three-site outer mismatch is
first upgraded to every nonnegative mismatch width.  At positive width we
choose the real cube root via `Real.rpow`; at width zero we take a decreasing
sequence of positive cubic windows and use order-closedness of `ENNReal`.

The four actual mismatch charts in
`ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily` differ from the
concrete chart only by a branch sign.  Their absolute near-mismatch events
are therefore exactly equal, as is their finite union.  Consequently the
family union retains the sharp displayed constant `840`, rather than losing
a factor of four to a union bound.

This module covers precisely the four-member ordinary outer family defined
in the imported module.  It does not claim an enumeration of every possible
iterated-`A2` history outside that displayed family.
-/

open scoped ENNReal

namespace
  ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Filter MeasureTheory Set

noncomputable section

/-! ## All-width cube-root wrapper -/

/-- The exact-zero near-mismatch event is null.  This is derived directly
from the positive cubic estimates, without adding an absolute-continuity
hypothesis: the bounds at `rho = 1 / (n + 1)` decrease to zero. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_zero :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent 0) = 0 := by
  apply le_antisymm
  · have hreal : Tendsto (fun n : Nat =>
        (1 : Real) / ((n : Real) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlimit : Tendsto (fun n : Nat =>
        840 * ENNReal.ofReal ((1 : Real) / ((n : Real) + 1)))
        atTop (nhds 0) := by
      have hscaledReal : Tendsto (fun n : Nat =>
          (840 : Real) * ((1 : Real) / ((n : Real) + 1)))
          atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hreal :
          Tendsto (fun n : Nat =>
            (840 : Real) * ((1 : Real) / ((n : Real) + 1)))
            atTop (nhds ((840 : Real) * 0)))
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 840)] using
        ENNReal.tendsto_ofReal hscaledReal
    apply ge_of_tendsto hlimit
    filter_upwards [] with n
    let rho : Real := 1 / ((n : Real) + 1)
    have hrho : 0 < rho := by
      dsimp [rho]
      positivity
    have hcube :=
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_cube_le hrho
    calc
      iidMassTripleLaw (threeSiteOuterNearMismatchEvent 0) ≤
          iidMassTripleLaw (threeSiteOuterNearMismatchEvent (rho ^ 3)) := by
        apply measure_mono
        intro triple htriple
        change |threeSiteOuterTripleMismatch triple| ≤ 0 at htriple
        change |threeSiteOuterTripleMismatch triple| ≤ rho ^ 3
        exact htriple.trans (by positivity)
      _ ≤ 840 * ENNReal.ofReal rho := hcube
      _ = 840 * ENNReal.ofReal
          ((1 : Real) / ((n : Real) + 1)) := rfl
  · exact bot_le

/-- All-width Hölder small-ball estimate.  The real quantity
`epsilon ^ ((3 : Real)⁻¹)` is the nonnegative cube root of `epsilon` when
`epsilon ≥ 0`; the theorem includes `epsilon = 0`. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_holder
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw (threeSiteOuterNearMismatchEvent epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) := by
  rcases hepsilon.eq_or_lt with rfl | hepsilon
  · simpa using iidMassTripleLaw_threeSiteOuterNearMismatchEvent_zero.le
  · have hroot : 0 < epsilon ^ ((3 : Real)⁻¹) :=
      Real.rpow_pos_of_pos hepsilon _
    have hcube :=
      iidMassTripleLaw_threeSiteOuterNearMismatchEvent_cube_le hroot
    have hcubeRoot :
        (epsilon ^ ((3 : Real)⁻¹)) ^ (3 : Nat) = epsilon := by
      simpa using Real.rpow_inv_natCast_pow (n := 3) hepsilon.le
        (by norm_num : (3 : Nat) ≠ 0)
    rw [hcubeRoot] at hcube
    exact hcube

/-! ## Transport to all four displayed ordinary outer histories -/

/-- The genuine actual mismatch chart for one displayed history, written in
the same three raw-mass coordinates as the quantitative theorem. -/
def threeSiteOrdinaryOuterHistoryTripleMismatch
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) : Real :=
  physlibIteratedA2PairMismatchChart
    (threeSiteOuterFrozenThirdBackground triple.2)
    (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
    firstPositivePhysicalModeThree
    (threeSiteOrdinaryOuterHistoryTerm index) triple.1

/-- Every displayed history chart is the concrete triple mismatch multiplied
by its original/conjugate branch sign. -/
theorem threeSiteOrdinaryOuterHistoryTripleMismatch_eq_branch_mul
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) :
    threeSiteOrdinaryOuterHistoryTripleMismatch index triple =
      firstPicardCoordinateBranchSign index.2 *
        threeSiteOuterTripleMismatch triple := by
  rw [threeSiteOrdinaryOuterHistoryTripleMismatch]
  rw [threeSiteOrdinaryOuterHistory_mismatchChart_eq_branch_mul_single]
  rw [threeSiteOuterTripleMismatch_secondMassLine_eq_pairChart
    triple triple.1.2]

/-- The branch sign disappears after taking absolute value. -/
theorem abs_threeSiteOrdinaryOuterHistoryTripleMismatch_eq
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (triple : MassTriple) :
    |threeSiteOrdinaryOuterHistoryTripleMismatch index triple| =
      |threeSiteOuterTripleMismatch triple| := by
  rw [threeSiteOrdinaryOuterHistoryTripleMismatch_eq_branch_mul, abs_mul]
  rcases index with ⟨slot, branch⟩
  fin_cases branch <;> simp [firstPicardCoordinateBranchSign]

/-- Near-mismatch event for one of the four actual ordinary outer-history
charts. -/
def threeSiteOrdinaryOuterHistoryNearMismatchEvent
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    Set MassTriple :=
  {triple |
    |threeSiteOrdinaryOuterHistoryTripleMismatch index triple| ≤ epsilon}

/-- Each one-history event is exactly the concrete near-mismatch event. -/
theorem threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon =
      threeSiteOuterNearMismatchEvent epsilon := by
  ext triple
  change |threeSiteOrdinaryOuterHistoryTripleMismatch index triple| ≤
      epsilon ↔ |threeSiteOuterTripleMismatch triple| ≤ epsilon
  rw [abs_threeSiteOrdinaryOuterHistoryTripleMismatch_eq]

theorem measurableSet_threeSiteOrdinaryOuterHistoryNearMismatchEvent
    (index : ThreeSiteOrdinaryOuterHistoryIndex) (epsilon : Real) :
    MeasurableSet
      (threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon) := by
  rw [threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq]
  exact measurableSet_threeSiteOuterNearMismatchEvent epsilon

/-- Uniform all-width Hölder estimate for each displayed ordinary outer
history. -/
theorem iidMassTripleLaw_threeSiteOrdinaryOuterHistoryNearMismatchEvent_le
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) := by
  rw [threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq]
  exact iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_holder hepsilon

/-- Finite union of the near-mismatch events of all four displayed ordinary
outer histories. -/
def threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
    (epsilon : Real) : Set MassTriple :=
  ⋃ index : ThreeSiteOrdinaryOuterHistoryIndex,
    threeSiteOrdinaryOuterHistoryNearMismatchEvent index epsilon

/-- Since all four events differ only by a sign before taking absolute value,
their union equals the concrete event exactly. -/
theorem threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq
    (epsilon : Real) :
    threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon =
      threeSiteOuterNearMismatchEvent epsilon := by
  apply le_antisymm
  · intro triple htriple
    obtain ⟨index, hindex⟩ := mem_iUnion.mp htriple
    rw [threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq] at hindex
    exact hindex
  · intro triple htriple
    apply mem_iUnion.mpr
    refine ⟨((0, 0) : ThreeSiteOrdinaryOuterHistoryIndex), ?_⟩
    rw [threeSiteOrdinaryOuterHistoryNearMismatchEvent_eq]
    exact htriple

theorem measurableSet_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent
    (epsilon : Real) :
    MeasurableSet
      (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon) := by
  rw [threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq]
  exact measurableSet_threeSiteOuterNearMismatchEvent epsilon

/-- Hölder small-ball estimate for the finite union of all four displayed
actual ordinary outer-history events.  No factor four is lost. -/
theorem
    iidMassTripleLaw_threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_le
    {epsilon : Real} (hepsilon : 0 ≤ epsilon) :
    iidMassTripleLaw
        (threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent epsilon) ≤
      840 * ENNReal.ofReal (epsilon ^ ((3 : Real)⁻¹)) := by
  rw [threeSiteOrdinaryOuterHistoryFamilyNearMismatchEvent_eq]
  exact iidMassTripleLaw_threeSiteOuterNearMismatchEvent_le_holder hepsilon

end

end
  ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterFamilyHolderSmallBall

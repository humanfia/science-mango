import ArchonPhysics.ActualEightSiteNarrowShiftedFamilyControl
import ArchonPhysics.ActualEightSiteNarrowUniformSimpleSpectrum
import ArchonPhysics.AdjugateWeightReindex

/-!
# Uniform projector-minor certificate on the narrow eight-site path

The selected shifted matrices are already known to stay within `10⁻³⁰` of
an exact rational center family.  Here that entrywise control is propagated
through each `8 × 8` adjugate and then through the nine selected quadratic
weights.  The exact center weights are evaluated from the certified adjugate
table and lie within the `10⁻⁶` budget of the fixed rational reference.
Together with uniform spectral simplicity, this proves that the genuine
selected projector minor never vanishes on the narrow interval.
-/

open scoped BigOperators Matrix
open Set

namespace ArchonPhysics.ActualEightSiteNarrowProjectorMinorCertificate

open ArchonPhysics
open ArchonPhysics.ActualEightSiteCenterAdjugateContractionCertificate
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge
open ArchonPhysics.ActualEightSiteNarrowShiftedFamilyControl
open ArchonPhysics.ActualEightSiteNarrowUniformSimpleSpectrum
open ArchonPhysics.AdjugateWeightReindex
open ArchonPhysics.FinEightAdjugateContractionPerturbation
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.SingleMassRankOnePerturbation

noncomputable section

/-- The three selected mass-perturbation directions in literal `Fin 8`
coordinates. -/
def actualEightSiteSelectedFinDirection : Fin 3 → Fin 8 → Real :=
  ![![0, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, -1]]

/-- Canonical reindexing sends each genuine cycle direction to its displayed
finite-coordinate vector. -/
theorem reindexVector_actualEightSiteSelectedDirection (s : Fin 3) :
    reindexVector (siteEquivFin 8)
        (cycleMassPerturbationVector (actualEightSiteSelectedSites s)) =
      actualEightSiteSelectedFinDirection s := by
  funext i
  fin_cases s <;> fin_cases i <;>
    norm_num +decide [reindexVector, actualEightSiteSelectedFinDirection,
      actualEightSiteSelectedSites, cycleMassPerturbationVector,
      differenceMatrix, siteEquivFin]

/-- The exact-center counterparts of the nine shifted-adjugate weights. -/
def actualEightSiteCenterAdjugateWeightMatrix :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s ↦ actualEightSiteSelectedFinDirection s ⬝ᵥ
    ((actualEightSiteCenterWeightedFamily r).adjugate *ᵥ
      actualEightSiteSelectedFinDirection s)

/-- The genuine site-indexed shifted-adjugate weights may be computed using
the reindexed finite shifted family and the displayed finite directions. -/
theorem actualEightSiteNarrowShiftedAdjugateWeightMatrix_eq_fin
    (t : Real) (r s : Fin 3) :
    actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s =
      actualEightSiteSelectedFinDirection s ⬝ᵥ
        ((actualEightSiteSelectedShiftedFamilyFin t r).adjugate *ᵥ
          actualEightSiteSelectedFinDirection s) := by
  have h := reindexVector_dotProduct_adjugate_reindex_mulVec
    (siteEquivFin 8)
    (orderedEigenvalueShiftedMatrix
      (fullEightDualHarmonic (actualEightSiteRationalMassPath t))
      (actualEightSiteDecayModes r))
    (cycleMassPerturbationVector (actualEightSiteSelectedSites s))
  rw [reindexVector_actualEightSiteSelectedDirection] at h
  simpa [actualEightSiteNarrowShiftedAdjugateWeightMatrix,
    orderedShiftedAdjugateWeightMatrix,
    actualEightSiteSelectedShiftedFamilyFin] using h.symm

theorem actualEightSiteSelectedFinDirection_abs_le_one
    (s : Fin 3) (i : Fin 8) :
    |actualEightSiteSelectedFinDirection s i| ≤ 1 := by
  fin_cases s <;> fin_cases i <;>
    norm_num [actualEightSiteSelectedFinDirection]

theorem actualEightSiteSelectedShiftedFamilyFin_entry_bound
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r : Fin 3) (i j : Fin 8) :
    |actualEightSiteSelectedShiftedFamilyFin t r i j| ≤ (21 : Real) / 4 := by
  calc
    |actualEightSiteSelectedShiftedFamilyFin t r i j| =
        |(actualEightSiteSelectedShiftedFamilyFin t r i j -
            actualEightSiteCenterWeightedFamily r i j) +
          actualEightSiteCenterWeightedFamily r i j| := by
      congr 1
      ring
    _ ≤ |actualEightSiteSelectedShiftedFamilyFin t r i j -
          actualEightSiteCenterWeightedFamily r i j| +
        |actualEightSiteCenterWeightedFamily r i j| := abs_add_le _ _
    _ ≤ (1 : Real) / 10 ^ 30 + 5 :=
      add_le_add
        (actualEightSiteSelectedShiftedFamilyFin_close_center ht r i j)
        (actualEightSiteCenterWeightedFamily_entry_bound r i j)
    _ ≤ (21 : Real) / 4 := by norm_num

theorem actualEightSiteCenterWeightedFamily_entry_bound_twenty_one_fourths
    (r : Fin 3) (i j : Fin 8) :
    |actualEightSiteCenterWeightedFamily r i j| ≤ (21 : Real) / 4 :=
  (actualEightSiteCenterWeightedFamily_entry_bound r i j).trans (by norm_num)

/-- Each physical adjugate entry remains close to its exact-center entry. -/
theorem actualEightSiteSelectedAdjugateEntry_close_center
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r : Fin 3) (i j : Fin 8) :
    |(actualEightSiteSelectedShiftedFamilyFin t r).adjugate i j -
      (actualEightSiteCenterWeightedFamily r).adjugate i j| ≤
        finEightAdjugateErrorBound ((21 : Real) / 4)
          ((1 : Real) / 10 ^ 30) := by
  exact abs_fin_eight_adjugate_entry_sub_le
    (actualEightSiteSelectedShiftedFamilyFin t r)
    (actualEightSiteCenterWeightedFamily r)
    ((21 : Real) / 4) ((1 : Real) / 10 ^ 30) (by norm_num)
    (actualEightSiteSelectedShiftedFamilyFin_entry_bound ht r)
    (actualEightSiteCenterWeightedFamily_entry_bound_twenty_one_fourths r)
    (actualEightSiteSelectedShiftedFamilyFin_close_center ht r) i j

/-- A uniform adjugate-entry estimate controls every selected quadratic
weight; the deliberately coarse factor `64` avoids relying on sparsity. -/
theorem actualEightSiteNarrowWeight_close_center
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r s : Fin 3) :
    |actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
      actualEightSiteCenterAdjugateWeightMatrix r s| ≤
        64 * finEightAdjugateErrorBound ((21 : Real) / 4)
          ((1 : Real) / 10 ^ 30) := by
  rw [actualEightSiteNarrowShiftedAdjugateWeightMatrix_eq_fin]
  unfold actualEightSiteCenterAdjugateWeightMatrix
  simp only [dotProduct, Matrix.mulVec]
  rw [← Finset.sum_sub_distrib]
  have hrewrite :
      (∑ x : Fin 8,
          (actualEightSiteSelectedFinDirection s x *
              ∑ y : Fin 8,
                (actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y *
                  actualEightSiteSelectedFinDirection s y -
            actualEightSiteSelectedFinDirection s x *
              ∑ y : Fin 8,
                (actualEightSiteCenterWeightedFamily r).adjugate x y *
                  actualEightSiteSelectedFinDirection s y)) =
        ∑ x : Fin 8, ∑ y : Fin 8,
          actualEightSiteSelectedFinDirection s x *
            ((actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y -
              (actualEightSiteCenterWeightedFamily r).adjugate x y) *
            actualEightSiteSelectedFinDirection s y := by
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  rw [hrewrite]
  calc
    |∑ x : Fin 8, ∑ y : Fin 8,
        actualEightSiteSelectedFinDirection s x *
          ((actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y -
            (actualEightSiteCenterWeightedFamily r).adjugate x y) *
          actualEightSiteSelectedFinDirection s y| ≤
        ∑ x : Fin 8, |∑ y : Fin 8,
          actualEightSiteSelectedFinDirection s x *
            ((actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y -
              (actualEightSiteCenterWeightedFamily r).adjugate x y) *
            actualEightSiteSelectedFinDirection s y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin 8, ∑ y : Fin 8,
        |actualEightSiteSelectedFinDirection s _x *
          ((actualEightSiteSelectedShiftedFamilyFin t r).adjugate _x y -
            (actualEightSiteCenterWeightedFamily r).adjugate _x y) *
          actualEightSiteSelectedFinDirection s y| := by
      apply Finset.sum_le_sum
      intro x _hx
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin 8, ∑ _y : Fin 8,
        finEightAdjugateErrorBound ((21 : Real) / 4)
          ((1 : Real) / 10 ^ 30) := by
      apply Finset.sum_le_sum
      intro x _hx
      apply Finset.sum_le_sum
      intro y _hy
      rw [abs_mul, abs_mul]
      have hAdjErrorNonneg : 0 ≤
          finEightAdjugateErrorBound ((21 : Real) / 4)
            ((1 : Real) / 10 ^ 30) := by
        norm_num [finEightAdjugateErrorBound]
      have hfirst :
          |actualEightSiteSelectedFinDirection s x| *
              |(actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y -
                (actualEightSiteCenterWeightedFamily r).adjugate x y| ≤
            1 * finEightAdjugateErrorBound ((21 : Real) / 4)
              ((1 : Real) / 10 ^ 30) :=
        mul_le_mul
          (actualEightSiteSelectedFinDirection_abs_le_one s x)
          (actualEightSiteSelectedAdjugateEntry_close_center ht r x y)
          (abs_nonneg _)
          (by positivity)
      calc
        |actualEightSiteSelectedFinDirection s x| *
              |(actualEightSiteSelectedShiftedFamilyFin t r).adjugate x y -
                (actualEightSiteCenterWeightedFamily r).adjugate x y| *
            |actualEightSiteSelectedFinDirection s y| ≤
            (1 * finEightAdjugateErrorBound ((21 : Real) / 4)
              ((1 : Real) / 10 ^ 30)) * 1 :=
          mul_le_mul hfirst
            (actualEightSiteSelectedFinDirection_abs_le_one s y)
            (abs_nonneg _) (by simpa using hAdjErrorNonneg)
        _ = finEightAdjugateErrorBound ((21 : Real) / 4)
              ((1 : Real) / 10 ^ 30) := by ring
    _ = 64 * finEightAdjugateErrorBound ((21 : Real) / 4)
          ((1 : Real) / 10 ^ 30) := by simp; ring

set_option maxHeartbeats 0 in
-- Nine exact quadratic-form comparisons expand the certified adjugate table.
/-- The explicit center table agrees with the low-denominator rational
reference to far better than one millionth in all nine entries. -/
theorem actualEightSiteCenterAdjugateWeightMatrix_close_reference
    (r s : Fin 3) :
    |actualEightSiteCenterAdjugateWeightMatrix r s -
      actualEightSiteNarrowRationalReferenceWeightMatrix r s| ≤
        (1 : Real) / 10 ^ 8 := by
  unfold actualEightSiteCenterAdjugateWeightMatrix
  rw [actualEightSiteCenterWeightedFamily_eq_centerShiftedReal]
  unfold centerShiftedReal
  have hmap := (Rat.castHom Real).map_adjugate (centerShifted r)
  change ((centerShifted r).adjugate).map ⇑(Rat.castHom Real) =
      ((centerShifted r).map ⇑(Rat.castHom Real)).adjugate at hmap
  rw [← hmap, ← centerAdjugateTable_eq_adjugate]
  fin_cases r <;> fin_cases s <;>
    norm_num [actualEightSiteSelectedFinDirection,
      actualEightSiteNarrowRationalReferenceWeightMatrix,
      centerAdjugateTable, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The nine genuine weights satisfy the `10⁻⁶` reference budget consumed by
the determinant-margin bridge. -/
theorem actualEightSiteNarrowShiftedAdjugateWeightMatrix_close_reference
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r s : Fin 3) :
    |actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
      actualEightSiteNarrowRationalReferenceWeightMatrix r s| ≤
        (1 : Real) / 1000000 := by
  calc
    |actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
        actualEightSiteNarrowRationalReferenceWeightMatrix r s| =
      |(actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
          actualEightSiteCenterAdjugateWeightMatrix r s) +
        (actualEightSiteCenterAdjugateWeightMatrix r s -
          actualEightSiteNarrowRationalReferenceWeightMatrix r s)| := by
      congr 1
      ring
    _ ≤ |actualEightSiteNarrowShiftedAdjugateWeightMatrix t r s -
          actualEightSiteCenterAdjugateWeightMatrix r s| +
        |actualEightSiteCenterAdjugateWeightMatrix r s -
          actualEightSiteNarrowRationalReferenceWeightMatrix r s| :=
      abs_add_le _ _
    _ ≤ 64 * finEightAdjugateErrorBound ((21 : Real) / 4)
          ((1 : Real) / 10 ^ 30) + (1 : Real) / 10 ^ 8 :=
      add_le_add (actualEightSiteNarrowWeight_close_center ht r s)
        (actualEightSiteCenterAdjugateWeightMatrix_close_reference r s)
    _ ≤ (1 : Real) / 1000000 := by
      norm_num [finEightAdjugateErrorBound]

/-- The genuine selected projector minor is nonzero throughout the complete
certified narrow interval. -/
theorem actualEightSiteSelectedProjectorMinor_ne_zero_on_narrow :
    ∀ t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper,
      actualEightSiteSelectedProjectorMinor
        (actualEightSiteRationalMassPath t) ≠ 0 := by
  apply actualEightSiteSelectedProjectorMinor_ne_zero_on_narrow_of_reference_error
  · intro t ht
    exact fullEightDualHarmonic_narrow_simpleOrderedSpectrum ht
  · intro t ht r s
    exact actualEightSiteNarrowShiftedAdjugateWeightMatrix_close_reference
      ht r s

end

end ArchonPhysics.ActualEightSiteNarrowProjectorMinorCertificate

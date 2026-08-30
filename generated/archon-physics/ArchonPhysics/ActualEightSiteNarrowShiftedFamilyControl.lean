import ArchonPhysics.ActualEightSiteNarrowSelectedEnergyControl
import ArchonPhysics.FinEightAdjugateContractionPerturbation
import ArchonPhysics.OrderedProjectorShiftedAdjugate

/-!
# Uniform shifted-family control on the narrow eight-site path

The physical shifted matrices for collision ranks `(3,5,6)` are uniformly
entrywise close to an exact rational center family.  The exact center
adjugate contraction is positive, so the physical contraction stays nonzero
throughout the whole narrow interval.
-/

open scoped BigOperators Matrix
open Set

namespace ArchonPhysics.ActualEightSiteNarrowShiftedFamilyControl

open ArchonPhysics
open ArchonPhysics.ActualEightSiteCenterAdjugateContractionCertificate
open ArchonPhysics.ActualEightSiteEndpointPhysicalTransport
open ArchonPhysics.ActualEightSiteEndpointBirdRootBoxes
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteNarrowPathSpectrumControl
open ArchonPhysics.ActualEightSiteNarrowProjectorMinorBridge
open ArchonPhysics.ActualEightSiteNarrowSelectedEnergyControl
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra
open ArchonPhysics.FinEightAdjugateContractionPerturbation
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorShiftedAdjugate
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble

noncomputable section

/-- The genuine physical shifted matrices, reindexed to literal `Fin 8`
coordinates. -/
def actualEightSiteSelectedShiftedFamilyFin
    (t : Real) : Fin 3 → Matrix (Fin 8) (Fin 8) Real :=
  fun r ↦
    Matrix.reindex (siteEquivFin 8) (siteEquivFin 8)
      (orderedEigenvalueShiftedMatrix
        (fullEightDualHarmonic (actualEightSiteRationalMassPath t))
        (actualEightSiteDecayModes r))

/-- On the physical support, the reindexed shifted family is the selected
eigenvalue times the identity minus the weighted-cycle Laplacian. -/
theorem actualEightSiteSelectedShiftedFamilyFin_eq_weighted
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r : Fin 3) :
    actualEightSiteSelectedShiftedFamilyFin t r =
      orderedEigenvalue (actualEightSitePathFinDual t)
          (actualEightSiteDecayModes r) •
        (1 : Matrix (Fin 8) (Fin 8) Real) -
      finWeightedCycleLaplacian (actualEightSitePathInverseMass t) := by
  have hspectrum :
      orderedEigenvalue
          (fullEightDualHarmonic (actualEightSiteRationalMassPath t))
            (actualEightSiteDecayModes r) =
        orderedEigenvalue (actualEightSitePathFinDual t)
          (actualEightSiteDecayModes r) := by
    calc
      _ = orderedEigenvalue (reindexedFullEightDual t)
          (actualEightSiteDecayModes r) :=
        orderedEigenvalue_fullEightDual_eq_reindexed t
          (actualEightSiteDecayModes r)
      _ = _ := by rw [← actualEightSitePathFinDual_eq_reindexed]
  have hweighted :
      (actualEightSitePathFinDual t).1 =
        finWeightedCycleLaplacian (actualEightSitePathInverseMass t) :=
    congrArg Subtype.val (actualEightSitePathFinDual_eq_finWeighted
      (actualEightSiteNarrow_mem_unit ht))
  unfold actualEightSiteSelectedShiftedFamilyFin
    orderedEigenvalueShiftedMatrix
  ext i j
  have hentry := congrFun (congrFun hweighted i) j
  change
    (fullEightDualHarmonic (actualEightSiteRationalMassPath t)).1
      ((siteEquivFin 8).symm i) ((siteEquivFin 8).symm j) =
      finWeightedCycleLaplacian (actualEightSitePathInverseMass t) i j
    at hentry
  simp [OrderedSingleModeProjector.matrixVal, Matrix.reindex_apply,
    Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, hspectrum, hentry]

/-- The exact real center family, written in the same weighted-cycle
coordinates used by the physical path. -/
def actualEightSiteCenterWeightedFamily :
    Fin 3 → Matrix (Fin 8) (Fin 8) Real :=
  fun r ↦ (centerEnergy r : Real) •
      (1 : Matrix (Fin 8) (Fin 8) Real) -
    finWeightedCycleLaplacian
      (actualEightSitePathInverseMass actualEightSiteNarrowCenter)

theorem centerInverseMass_cast_eq_pathCenter (i : Fin 8) :
    (centerInverseMass i : Real) =
      actualEightSitePathInverseMass actualEightSiteNarrowCenter i := by
  fin_cases i <;>
    norm_num [centerInverseMass, actualEightSitePathInverseMass,
      actualEightSiteRationalMassPath, actualEightSiteNarrowCenter,
      actualEightSiteNarrowLower, actualEightSiteNarrowUpper]


private def genericEightShifted
    (q : Rat) (v : Fin 8 → Rat) : Matrix (Fin 8) (Fin 8) Rat :=
  !![q-v 0-v 1, v 1, 0, 0, 0, 0, 0, v 0;
     v 1, q-v 1-v 2, v 2, 0, 0, 0, 0, 0;
     0, v 2, q-v 2-v 3, v 3, 0, 0, 0, 0;
     0, 0, v 3, q-v 3-v 4, v 4, 0, 0, 0;
     0, 0, 0, v 4, q-v 4-v 5, v 5, 0, 0;
     0, 0, 0, 0, v 5, q-v 5-v 6, v 6, 0;
     0, 0, 0, 0, 0, v 6, q-v 6-v 7, v 7;
     v 0, 0, 0, 0, 0, 0, v 7, q-v 7-v 0]

private def genericEightRationalDualShifted
    (q : Rat) (v : Fin 8 → Rat) : Matrix (Fin 8) (Fin 8) Rat :=
  q • (1 : Matrix (Fin 8) (Fin 8) Rat) - rationalDualCycleMatrix v

private theorem genericEightRationalDualShifted_row_zero
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 0 j =
      genericEightShifted q v 0 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_one
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 1 j =
      genericEightShifted q v 1 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_two
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 2 j =
      genericEightShifted q v 2 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_three
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 3 j =
      genericEightShifted q v 3 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_four
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 4 j =
      genericEightShifted q v 4 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_five
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 5 j =
      genericEightShifted q v 5 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_six
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 6 j =
      genericEightShifted q v 6 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_row_seven
    (q : Rat) (v : Fin 8 → Rat) (j : Fin 8) :
    genericEightRationalDualShifted q v 7 j =
      genericEightShifted q v 7 j := by
  fin_cases j <;>
    simp [genericEightRationalDualShifted, genericEightShifted,
      rationalDualCycleMatrix, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

private theorem genericEightRationalDualShifted_eq
    (q : Rat) (v : Fin 8 → Rat) :
    genericEightRationalDualShifted q v = genericEightShifted q v := by
  ext i j
  fin_cases i
  · exact genericEightRationalDualShifted_row_zero q v j
  · exact genericEightRationalDualShifted_row_one q v j
  · exact genericEightRationalDualShifted_row_two q v j
  · exact genericEightRationalDualShifted_row_three q v j
  · exact genericEightRationalDualShifted_row_four q v j
  · exact genericEightRationalDualShifted_row_five q v j
  · exact genericEightRationalDualShifted_row_six q v j
  · exact genericEightRationalDualShifted_row_seven q v j

private def actualEightSiteCenterRatFamily :
    Fin 3 → Matrix (Fin 8) (Fin 8) Rat :=
  fun r ↦ genericEightRationalDualShifted (centerEnergy r) centerInverseMass

private theorem actualEightSiteCenterRatFamily_eq_centerShifted :
    actualEightSiteCenterRatFamily = centerShifted := by
  funext r
  change genericEightRationalDualShifted (centerEnergy r) centerInverseMass =
    genericEightShifted (centerEnergy r) centerInverseMass
  exact genericEightRationalDualShifted_eq (centerEnergy r) centerInverseMass

private theorem genericEightRationalDualShifted_map
    (q : Rat) (v : Fin 8 → Rat) :
    (q : Real) • (1 : Matrix (Fin 8) (Fin 8) Real) -
        (rationalDualCycleMatrix v).map (Rat.castHom Real) =
      (genericEightRationalDualShifted q v).map (Rat.castHom Real) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [genericEightRationalDualShifted, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply]
  · simp [genericEightRationalDualShifted, Matrix.one_apply,
      Matrix.sub_apply, Matrix.smul_apply, hij]

private def actualEightSiteCenterRationalDualFamily :
    Fin 3 → Matrix (Fin 8) (Fin 8) Real :=
  fun r ↦ (centerEnergy r : Real) •
      (1 : Matrix (Fin 8) (Fin 8) Real) -
    (rationalDualCycleMatrix centerInverseMass).map (Rat.castHom Real)

private theorem actualEightSiteCenterRationalDualFamily_eq_map_rat :
    actualEightSiteCenterRationalDualFamily =
      fun r ↦ (actualEightSiteCenterRatFamily r).map (Rat.castHom Real) := by
  funext r
  change (centerEnergy r : Real) •
      (1 : Matrix (Fin 8) (Fin 8) Real) -
        (rationalDualCycleMatrix centerInverseMass).map (Rat.castHom Real) =
    (genericEightRationalDualShifted
      (centerEnergy r) centerInverseMass).map (Rat.castHom Real)
  exact genericEightRationalDualShifted_map
    (centerEnergy r) centerInverseMass

/-- The weighted-cycle center family is exactly the real image of the
kernel-certified rational center matrices. -/
theorem actualEightSiteCenterWeightedFamily_eq_centerShiftedReal :
    actualEightSiteCenterWeightedFamily = centerShiftedReal := by
  have hweights :
      actualEightSitePathInverseMass actualEightSiteNarrowCenter =
        fun i ↦ (centerInverseMass i : Real) := by
    funext i
    exact (centerInverseMass_cast_eq_pathCenter i).symm
  rw [show actualEightSiteCenterWeightedFamily =
      fun r ↦ (centerEnergy r : Real) •
          (1 : Matrix (Fin 8) (Fin 8) Real) -
        finWeightedCycleLaplacian (fun i ↦ (centerInverseMass i : Real)) by
    unfold actualEightSiteCenterWeightedFamily
    rw [hweights]]
  rw [ActualEightSiteNarrowEndpointPhysicalTransport.finWeightedCycleLaplacian_ratCast_eq_rationalDualCycleMatrix
      centerInverseMass]
  change actualEightSiteCenterRationalDualFamily = centerShiftedReal
  calc
    actualEightSiteCenterRationalDualFamily =
        fun r ↦ (actualEightSiteCenterRatFamily r).map (Rat.castHom Real) :=
      actualEightSiteCenterRationalDualFamily_eq_map_rat
    _ = fun r ↦ (centerShifted r).map (Rat.castHom Real) := by
      rw [actualEightSiteCenterRatFamily_eq_centerShifted]
    _ = centerShiftedReal := rfl

/-- Every physical shifted entry is within `10⁻³⁰` of the exact center. -/
theorem actualEightSiteSelectedShiftedFamilyFin_close_center
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper)
    (r : Fin 3) (i j : Fin 8) :
    |actualEightSiteSelectedShiftedFamilyFin t r i j -
      actualEightSiteCenterWeightedFamily r i j| ≤
        (1 : Real) / 10 ^ 30 := by
  rw [actualEightSiteSelectedShiftedFamilyFin_eq_weighted ht r]
  have he := actualEightSiteSelectedEnergy_close_center ht r
  have hL := actualEightSiteNarrowLaplacian_close_center t ht i j
  have hone : |(1 : Matrix (Fin 8) (Fin 8) Real) i j| ≤ 1 := by
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, hij]
  have henergyTerm :
      |orderedEigenvalue (actualEightSitePathFinDual t)
          (actualEightSiteDecayModes r) - (centerEnergy r : Real)| *
        |(1 : Matrix (Fin 8) (Fin 8) Real) i j| ≤
          (1 : Real) / 10 ^ 34 := by
    calc
      _ ≤ ((1 : Real) / 10 ^ 34) * 1 :=
        mul_le_mul he hone (abs_nonneg _)
          (by norm_num : (0 : Real) ≤ (1 : Real) / 10 ^ 34)
      _ = (1 : Real) / 10 ^ 34 := mul_one _
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    |(orderedEigenvalue (actualEightSitePathFinDual t)
          (actualEightSiteDecayModes r) *
            (1 : Matrix (Fin 8) (Fin 8) Real) i j -
        finWeightedCycleLaplacian (actualEightSitePathInverseMass t) i j) -
      ((centerEnergy r : Real) *
            (1 : Matrix (Fin 8) (Fin 8) Real) i j -
        finWeightedCycleLaplacian
          (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
            i j)| =
        |(orderedEigenvalue (actualEightSitePathFinDual t)
            (actualEightSiteDecayModes r) - (centerEnergy r : Real)) *
              (1 : Matrix (Fin 8) (Fin 8) Real) i j -
          (finWeightedCycleLaplacian (actualEightSitePathInverseMass t) i j -
            finWeightedCycleLaplacian
              (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
                i j)| := by
      congr 1
      ring
    _ ≤ |(orderedEigenvalue (actualEightSitePathFinDual t)
            (actualEightSiteDecayModes r) - (centerEnergy r : Real)) *
              (1 : Matrix (Fin 8) (Fin 8) Real) i j| +
          |finWeightedCycleLaplacian (actualEightSitePathInverseMass t) i j -
            finWeightedCycleLaplacian
              (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
                i j| := by
      calc
        _ = |((orderedEigenvalue (actualEightSitePathFinDual t)
                (actualEightSiteDecayModes r) - (centerEnergy r : Real)) *
                  (1 : Matrix (Fin 8) (Fin 8) Real) i j) +
              (-(finWeightedCycleLaplacian
                  (actualEightSitePathInverseMass t) i j -
                finWeightedCycleLaplacian
                  (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
                    i j))| := by rw [sub_eq_add_neg]
        _ ≤ |(orderedEigenvalue (actualEightSitePathFinDual t)
                (actualEightSiteDecayModes r) - (centerEnergy r : Real)) *
                  (1 : Matrix (Fin 8) (Fin 8) Real) i j| +
              |-(finWeightedCycleLaplacian
                  (actualEightSitePathInverseMass t) i j -
                finWeightedCycleLaplacian
                  (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
                    i j)| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ = |orderedEigenvalue (actualEightSitePathFinDual t)
            (actualEightSiteDecayModes r) - (centerEnergy r : Real)| *
          |(1 : Matrix (Fin 8) (Fin 8) Real) i j| +
        |finWeightedCycleLaplacian (actualEightSitePathInverseMass t) i j -
          finWeightedCycleLaplacian
            (actualEightSitePathInverseMass actualEightSiteNarrowCenter)
              i j| := by rw [abs_mul]
    _ ≤ (1 : Real) / 10 ^ 34 + (1 : Real) / 10 ^ 31 :=
      add_le_add henergyTerm hL
    _ ≤ (1 : Real) / 10 ^ 30 := by norm_num

theorem actualEightSiteCenterWeightedFamily_entry_bound
    (r : Fin 3) (i j : Fin 8) :
    |actualEightSiteCenterWeightedFamily r i j| ≤ 5 := by
  rw [actualEightSiteCenterWeightedFamily_eq_centerShiftedReal]
  have henergy_nonneg : 0 ≤ (centerEnergy r : Real) := by
    fin_cases r <;> norm_num [centerEnergy]
  have henergy_le : (centerEnergy r : Real) ≤ (5 : Real) / 2 := by
    fin_cases r <;> norm_num [centerEnergy]
  fin_cases i <;> fin_cases j
  all_goals
    simp [centerShiftedReal, centerShifted, centerInverseMass]
  all_goals rw [abs_le]
  all_goals constructor <;> norm_num <;> linarith

/-- Reindexing does not change the physical adjugate contraction. -/
theorem actualEightSiteSelectedDualAdjugateContraction_eq_fin (t : Real) :
    actualEightSiteSelectedDualAdjugateContraction
        (actualEightSiteRationalMassPath t) =
      adjugateEntryProductContraction
        (actualEightSiteSelectedShiftedFamilyFin t) := by
  unfold actualEightSiteSelectedDualAdjugateContraction
    harmonicDualOrderedAdjugateInteractionContraction
    actualEightSiteSelectedShiftedFamilyFin
  exact
    (adjugateEntryProductContraction_reindex
      (siteEquivFin 8)
      (fun r ↦
        orderedEigenvalueShiftedMatrix
          (fullEightDualHarmonic (actualEightSiteRationalMassPath t))
          (actualEightSiteDecayModes r))).symm

/-- The physical dual-adjugate contraction is positive throughout the
certified narrow interval. -/
theorem actualEightSiteSelectedDualAdjugateContraction_pos
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper) :
    0 < actualEightSiteSelectedDualAdjugateContraction
      (actualEightSiteRationalMassPath t) := by
  rw [actualEightSiteSelectedDualAdjugateContraction_eq_fin]
  apply fin_eight_adjugate_contraction_pos_of_close
    (actualEightSiteSelectedShiftedFamilyFin t)
    actualEightSiteCenterWeightedFamily
    ((21 : Real) / 4) ((1 : Real) / 10 ^ 30) ((3 : Real) / 8)
  · norm_num
  · intro r i j
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
  · intro r i j
    exact (actualEightSiteCenterWeightedFamily_entry_bound r i j).trans
      (by norm_num)
  · exact actualEightSiteSelectedShiftedFamilyFin_close_center ht
  · rw [actualEightSiteCenterWeightedFamily_eq_centerShiftedReal]
    exact centerShiftedReal_contraction_gt_three_eighths
  · norm_num [finEightContractionErrorBound,
      finEightAdjugateErrorBound, finEightAdjugateBound]

theorem actualEightSiteSelectedDualAdjugateContraction_ne_zero
    {t : Real}
    (ht : t ∈ Icc actualEightSiteNarrowLower actualEightSiteNarrowUpper) :
    actualEightSiteSelectedDualAdjugateContraction
      (actualEightSiteRationalMassPath t) ≠ 0 :=
  ne_of_gt (actualEightSiteSelectedDualAdjugateContraction_pos ht)

end

end ArchonPhysics.ActualEightSiteNarrowShiftedFamilyControl

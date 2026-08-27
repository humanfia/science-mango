import ArchonPhysics.RepeatedParentChildMismatchSmallBall
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Quadratic small-ball bounds survive probability weak limits

A uniform finite-volume estimate on every closed symmetric mismatch window
controls the corresponding open window in a weak probability limit by the
open-set half of Portmanteau.  Sending the window radius to zero then removes
the zero-frequency atom.  This is the generic limit step needed by the two
repeated parent--child sectors.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.QuadraticSmallBallWeakLimit

open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- The open symmetric mismatch window. -/
def openAbsoluteMismatchSublevel (delta : Real) : Set Real :=
  {mismatch | |mismatch| < delta}

theorem openAbsoluteMismatchSublevel_isOpen (delta : Real) :
    IsOpen (openAbsoluteMismatchSublevel delta) := by
  exact isOpen_lt continuous_abs continuous_const

theorem openAbsoluteMismatchSublevel_subset_absoluteMismatchSublevel
    (delta : Real) :
    openAbsoluteMismatchSublevel delta ⊆ absoluteMismatchSublevel delta := by
  intro mismatch hmismatch
  change |mismatch| < delta at hmismatch
  change |mismatch| ≤ delta
  exact hmismatch.le

theorem singleton_zero_subset_openAbsoluteMismatchSublevel
    {delta : Real} (hdelta : 0 < delta) :
    ({0} : Set Real) ⊆ openAbsoluteMismatchSublevel delta := by
  intro mismatch hmismatch
  simp only [Set.mem_singleton_iff] at hmismatch
  subst mismatch
  simpa [openAbsoluteMismatchSublevel] using hdelta

/-- A uniform `C * delta^2` small-ball estimate for a weakly convergent
sequence of probability measures rules out a zero atom in the limit.

The source estimate is deliberately stated on the closed window
`|mismatch| <= delta`: its restriction to the open window combines with the
open-set Portmanteau inequality in the useful direction. -/
theorem probabilityMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (source : Nat → ProbabilityMeasure Real)
    (target : ProbabilityMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (C : Real) (hC : 0 ≤ C)
    (hbound : ∀ n : Nat, ∀ delta : Real,
      0 < delta → delta ≤ 1 →
      ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤ C * delta ^ 2) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  let tolerance : Nat → Real := fun n => 1 / ((n : Real) + 1)
  let upper : Nat → Real := fun n => C * tolerance n ^ 2
  have htolerance_pos (n : Nat) : 0 < tolerance n := by
    dsimp [tolerance]
    positivity
  have htolerance_le_one (n : Nat) : tolerance n ≤ 1 := by
    dsimp [tolerance]
    exact (div_le_one (by positivity : (0 : Real) < (n : Real) + 1)).2
      (by
        have hn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
        linarith)
  have hopenBound (delta : Real) (hdelta : 0 < delta)
      (hdelta1 : delta ≤ 1) :
      (target : Measure Real) (openAbsoluteMismatchSublevel delta) ≤
        ENNReal.ofReal (C * delta ^ 2) := by
    have hopen := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlimit
      (openAbsoluteMismatchSublevel_isOpen delta)
    have hconstant_nonneg : 0 ≤ C * delta ^ 2 :=
      mul_nonneg hC (sq_nonneg delta)
    have hsourceENN : ∀ n : Nat,
        (source n : Measure Real) (openAbsoluteMismatchSublevel delta) ≤
          ENNReal.ofReal (C * delta ^ 2) := by
      intro n
      have hclosedReal := hbound n delta hdelta hdelta1
      have hopenReal :
          ((source n : Measure Real)
              (openAbsoluteMismatchSublevel delta)).toReal ≤
            C * delta ^ 2 := by
        exact (ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono
            (openAbsoluteMismatchSublevel_subset_absoluteMismatchSublevel
              delta))).trans hclosedReal
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hconstant_nonneg]
      exact hopenReal
    have hliminf :
        atTop.liminf (fun n : Nat =>
          (source n : Measure Real) (openAbsoluteMismatchSublevel delta)) ≤
          ENNReal.ofReal (C * delta ^ 2) := by
      calc
        atTop.liminf (fun n : Nat =>
            (source n : Measure Real) (openAbsoluteMismatchSublevel delta)) ≤
            atTop.liminf (fun _n : Nat =>
              ENNReal.ofReal (C * delta ^ 2)) :=
          Filter.liminf_le_liminf (Eventually.of_forall hsourceENN)
        _ = ENNReal.ofReal (C * delta ^ 2) := by simp
    exact hopen.trans hliminf
  have hle (n : Nat) :
      ((target : Measure Real) ({0} : Set Real)).toReal ≤ upper n := by
    have htargetENN :
        (target : Measure Real) ({0} : Set Real) ≤
          ENNReal.ofReal (upper n) := by
      calc
        (target : Measure Real) ({0} : Set Real) ≤
            (target : Measure Real)
              (openAbsoluteMismatchSublevel (tolerance n)) :=
          measure_mono
            (singleton_zero_subset_openAbsoluteMismatchSublevel
              (htolerance_pos n))
        _ ≤ ENNReal.ofReal (C * tolerance n ^ 2) :=
          hopenBound (tolerance n) (htolerance_pos n)
            (htolerance_le_one n)
        _ = ENNReal.ofReal (upper n) := rfl
    have hupper_nonneg : 0 ≤ upper n := by
      dsimp [upper]
      exact mul_nonneg hC (sq_nonneg _)
    have htargetReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr htargetENN
    simpa [ENNReal.toReal_ofReal hupper_nonneg] using htargetReal
  have htolerance : Tendsto tolerance atTop (nhds 0) := by
    change Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hsquare : Tendsto (fun n => tolerance n ^ 2) atTop (nhds 0) := by
      simpa using htolerance.pow 2
    have hmul :=
      (tendsto_const_nhds :
        Tendsto (fun _n : Nat => C) atTop (nhds C)).mul hsquare
    simpa [upper] using hmul
  have hrealZero :
      ((target : Measure Real) ({0} : Set Real)).toReal = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hupper hle
    · exact ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff
    ((target : Measure Real) ({0} : Set Real))).mp hrealZero with hzero | htop
  · exact hzero
  · exact (measure_ne_top (target : Measure Real) ({0} : Set Real) htop).elim

end

end ArchonPhysics.QuadraticSmallBallWeakLimit

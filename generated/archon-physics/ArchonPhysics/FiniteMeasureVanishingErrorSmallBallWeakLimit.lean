import ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit

/-!
# Small-ball bounds with a vanishing finite-volume error

Finite-volume empirical spectral measures are atomic, so domination by
Lebesgue measure at every volume is impossible.  The stable input for a weak
limit is instead a small-ball estimate

`mu_N {|x| <= delta} <= C * delta + error_N`,

where `error_N -> 0`.  This file proves that such an estimate rules out an
atom at zero for probability and arbitrary finite-measure weak limits.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit

open ArchonPhysics.QuadraticSmallBallWeakLimit
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- A uniform linear small-ball estimate, up to an error vanishing with the
volume, removes the zero atom from a probability weak limit. -/
theorem probabilityMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
    (source : Nat → ProbabilityMeasure Real)
    (target : ProbabilityMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (C : Real) (hC : 0 ≤ C)
    (error : Nat → Real) (herror_nonneg : ∀ n, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n : Nat, ∀ delta : Real,
      0 < delta → delta ≤ 1 →
      ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤
        C * delta + error n) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  have hopenBound (delta : Real) (hdelta : 0 < delta)
      (hdelta1 : delta ≤ 1) :
      (target : Measure Real) (openAbsoluteMismatchSublevel delta) ≤
        ENNReal.ofReal (C * delta) := by
    have hopen := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlimit
      (openAbsoluteMismatchSublevel_isOpen delta)
    have hsourceENN : ∀ n : Nat,
        (source n : Measure Real) (openAbsoluteMismatchSublevel delta) ≤
          ENNReal.ofReal (C * delta + error n) := by
      intro n
      have hclosedReal := hbound n delta hdelta hdelta1
      have hopenReal :
          ((source n : Measure Real)
              (openAbsoluteMismatchSublevel delta)).toReal ≤
            C * delta + error n := by
        exact (ENNReal.toReal_mono (measure_ne_top _ _)
          (measure_mono
            (openAbsoluteMismatchSublevel_subset_absoluteMismatchSublevel
              delta))).trans hclosedReal
      have hupper_nonneg : 0 ≤ C * delta + error n :=
        add_nonneg (mul_nonneg hC hdelta.le) (herror_nonneg n)
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hupper_nonneg]
      exact hopenReal
    have hupperReal : Tendsto (fun n => C * delta + error n)
        atTop (nhds (C * delta)) := by
      simpa using
        (tendsto_const_nhds.add herror :
          Tendsto (fun n => C * delta + error n)
            atTop (nhds (C * delta + 0)))
    have hupperENN : Tendsto
        (fun n => ENNReal.ofReal (C * delta + error n))
        atTop (nhds (ENNReal.ofReal (C * delta))) :=
      ENNReal.tendsto_ofReal hupperReal
    have hliminf :
        atTop.liminf (fun n : Nat =>
          (source n : Measure Real) (openAbsoluteMismatchSublevel delta)) ≤
          ENNReal.ofReal (C * delta) := by
      calc
        atTop.liminf (fun n : Nat =>
            (source n : Measure Real) (openAbsoluteMismatchSublevel delta)) ≤
            atTop.liminf (fun n : Nat =>
              ENNReal.ofReal (C * delta + error n)) :=
          Filter.liminf_le_liminf (Eventually.of_forall hsourceENN)
        _ = ENNReal.ofReal (C * delta) := hupperENN.liminf_eq
    exact hopen.trans hliminf
  let tolerance : Nat → Real := fun n => 1 / ((n : Real) + 1)
  let upper : Nat → Real := fun n => C * tolerance n
  have htolerance_pos (n : Nat) : 0 < tolerance n := by
    dsimp [tolerance]
    positivity
  have htolerance_le_one (n : Nat) : tolerance n ≤ 1 := by
    dsimp [tolerance]
    exact (div_le_one (by positivity : (0 : Real) < (n : Real) + 1)).2
      (by
        have hn : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
        linarith)
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
        _ ≤ ENNReal.ofReal (C * tolerance n) :=
          hopenBound (tolerance n) (htolerance_pos n)
            (htolerance_le_one n)
        _ = ENNReal.ofReal (upper n) := rfl
    have hupper_nonneg : 0 ≤ upper n := by
      exact mul_nonneg hC (htolerance_pos n).le
    have htargetReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr htargetENN
    simpa [ENNReal.toReal_ofReal hupper_nonneg] using htargetReal
  have htolerance : Tendsto tolerance atTop (nhds 0) := by
    change Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _n : Nat => C) atTop (nhds C)).mul
        htolerance
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

/-- Finite-measure version.  No lower bound on source masses is assumed; a
nonzero target supplies one eventually after passing to a tail and
normalizing. -/
theorem finiteMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
    (source : Nat → FiniteMeasure Real)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (C : Real) (hC : 0 ≤ C)
    (error : Nat → Real) (herror_nonneg : ∀ n, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n : Nat, ∀ delta : Real,
      0 < delta → delta ≤ 1 →
      ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤
        C * delta + error n) :
    (target : Measure Real) ({0} : Set Real) = 0 := by
  by_cases htarget : target = 0
  · simp [htarget]
  have htargetMass : target.mass ≠ 0 := target.mass_nonzero_iff.mpr htarget
  have htargetMass_pos : 0 < target.mass := pos_iff_ne_zero.mpr htargetMass
  let lowerMass : NNReal := target.mass / 2
  have hlowerMass_pos : 0 < lowerMass := by
    dsimp [lowerMass]
    positivity
  have hlowerMass_lt : lowerMass < target.mass := by
    dsimp [lowerMass]
    exact div_lt_self htargetMass_pos (by norm_num)
  have hmass : Tendsto (fun n => (source n).mass) atTop
      (nhds target.mass) := hlimit.mass
  have hmassLowerEventually :
      ∀ᶠ n in atTop, lowerMass < (source n).mass :=
    hmass.eventually (Ioi_mem_nhds hlowerMass_lt)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmassLowerEventually
  let tail : Nat → FiniteMeasure Real := fun j => source (j + N)
  have htailLower (j : Nat) : lowerMass < (tail j).mass := by
    dsimp [tail]
    exact hN (j + N) (Nat.le_add_left N j)
  have htailNonzero (j : Nat) : tail j ≠ 0 :=
    (tail j).mass_nonzero_iff.mp
      (ne_of_gt (hlowerMass_pos.trans (htailLower j)))
  have hnormalize : Tendsto (fun n => (source n).normalize) atTop
      (nhds target.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hlimit htarget
  have hnormalizeTail : Tendsto (fun j => (tail j).normalize) atTop
      (nhds target.normalize) := by
    change Tendsto
      ((fun n => (source n).normalize) ∘ (fun j : Nat => j + N))
      atTop (nhds target.normalize)
    exact hnormalize.comp (tendsto_add_atTop_nat N)
  let normalizedConstant : Real := (lowerMass : Real)⁻¹ * C
  let normalizedError : Nat → Real := fun j =>
    (lowerMass : Real)⁻¹ * error (j + N)
  have hnormalizedConstant_nonneg : 0 ≤ normalizedConstant := by
    exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg lowerMass)) hC
  have hnormalizedError_nonneg (j : Nat) : 0 ≤ normalizedError j := by
    exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg lowerMass))
      (herror_nonneg (j + N))
  have hnormalizedError : Tendsto normalizedError atTop (nhds 0) := by
    have htailError : Tendsto (fun j => error (j + N)) atTop (nhds 0) :=
      herror.comp (tendsto_add_atTop_nat N)
    have hmul :=
      (tendsto_const_nhds : Tendsto
        (fun _j : Nat => (lowerMass : Real)⁻¹) atTop
          (nhds (lowerMass : Real)⁻¹)).mul htailError
    simpa [normalizedError] using hmul
  have hnormalizedBound (j : Nat) (delta : Real)
      (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
      (((tail j).normalize : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤
        normalizedConstant * delta + normalizedError j := by
    have hraw := hbound (j + N) delta hdelta hdelta1
    have hlowerReal : (lowerMass : Real) ≤ ((tail j).mass : Real) := by
      exact_mod_cast (htailLower j).le
    have htailMass_pos : 0 < ((tail j).mass : Real) := by
      exact_mod_cast (htailLower j).trans' hlowerMass_pos
    have hlowerReal_pos : 0 < (lowerMass : Real) := by
      exact_mod_cast hlowerMass_pos
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
      (tail j) (htailNonzero j), Measure.smul_apply,
      ENNReal.toReal_smul]
    change ((tail j).mass : Real)⁻¹ *
        (((tail j : FiniteMeasure Real) : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤
      normalizedConstant * delta + normalizedError j
    calc
      ((tail j).mass : Real)⁻¹ *
          (((tail j : FiniteMeasure Real) : Measure Real)
            (absoluteMismatchSublevel delta)).toReal ≤
        ((tail j).mass : Real)⁻¹ *
          (C * delta + error (j + N)) := by
            exact mul_le_mul_of_nonneg_left hraw
              (inv_nonneg.mpr htailMass_pos.le)
      _ ≤ (lowerMass : Real)⁻¹ *
          (C * delta + error (j + N)) := by
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ htailMass_pos hlowerReal_pos).2 hlowerReal)
          (add_nonneg (mul_nonneg hC hdelta.le)
            (herror_nonneg (j + N)))
      _ = normalizedConstant * delta + normalizedError j := by
        dsimp [normalizedConstant, normalizedError]
        ring
  have hnormalizedZero :=
    probabilityMeasure_singleton_zero_eq_zero_of_linearSmallBall_with_vanishingError
      (fun j => (tail j).normalize) target.normalize hnormalizeTail
      normalizedConstant hnormalizedConstant_nonneg
      normalizedError hnormalizedError_nonneg hnormalizedError
      hnormalizedBound
  have hnormalizedZeroNN : target.normalize ({0} : Set Real) = 0 :=
    (ProbabilityMeasure.null_iff_toMeasure_null
      target.normalize ({0} : Set Real)).2 hnormalizedZero
  have hself := target.self_eq_mass_mul_normalize ({0} : Set Real)
  rw [hnormalizedZeroNN, mul_zero] at hself
  exact (FiniteMeasure.null_iff_toMeasure_null
    target ({0} : Set Real)).1 hself

end


end ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit

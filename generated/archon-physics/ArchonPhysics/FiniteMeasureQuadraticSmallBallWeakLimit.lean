import ArchonPhysics.QuadraticSmallBallWeakLimit

/-!
# Quadratic small-ball bounds survive finite-measure weak limits

The repeated-sector measures are finite per-site measures rather than
probability measures.  If the finite weak limit is zero there is nothing to
prove.  Otherwise, convergence of total masses supplies a positive lower
bound on a tail; normalizing that tail reduces the result to the probability
small-ball theorem without assuming a sector-mass lower bound a priori.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit

open ArchonPhysics.QuadraticSmallBallWeakLimit
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- A uniform `C * delta^2` small-ball estimate rules out a zero atom in every
finite-measure weak limit.  No positive lower bound on the source masses is an
assumption: in the nonzero-limit branch it follows eventually from weak
convergence, while the zero-limit branch is immediate. -/
theorem finiteMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
    (source : Nat → FiniteMeasure Real)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto source atTop (nhds target))
    (C : Real) (hC : 0 ≤ C)
    (hbound : ∀ n : Nat, ∀ delta : Real,
      0 < delta → delta ≤ 1 →
      ((source n : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤ C * delta ^ 2) :
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
  have hmass :
      Tendsto (fun n => (source n).mass) atTop (nhds target.mass) :=
    hlimit.mass
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
  have hnormalize :
      Tendsto (fun n => (source n).normalize) atTop
        (nhds target.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hlimit htarget
  have hnormalizeTail :
      Tendsto (fun j => (tail j).normalize) atTop
        (nhds target.normalize) := by
    change Tendsto
      ((fun n => (source n).normalize) ∘ (fun j : Nat => j + N))
      atTop (nhds target.normalize)
    exact hnormalize.comp (tendsto_add_atTop_nat N)
  let normalizedConstant : Real := (lowerMass : Real)⁻¹ * C
  have hnormalizedConstant_nonneg : 0 ≤ normalizedConstant := by
    dsimp [normalizedConstant]
    exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg lowerMass)) hC
  have hnormalizedBound (j : Nat) (delta : Real)
      (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
      (((tail j).normalize : Measure Real)
          (absoluteMismatchSublevel delta)).toReal ≤
        normalizedConstant * delta ^ 2 := by
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
      normalizedConstant * delta ^ 2
    calc
      ((tail j).mass : Real)⁻¹ *
          (((tail j : FiniteMeasure Real) : Measure Real)
            (absoluteMismatchSublevel delta)).toReal ≤
        ((tail j).mass : Real)⁻¹ * (C * delta ^ 2) := by
          exact mul_le_mul_of_nonneg_left hraw
            (inv_nonneg.mpr htailMass_pos.le)
      _ ≤ (lowerMass : Real)⁻¹ * (C * delta ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ htailMass_pos hlowerReal_pos).2 hlowerReal)
          (mul_nonneg hC (sq_nonneg delta))
      _ = normalizedConstant * delta ^ 2 := by
        dsimp [normalizedConstant]
        ring
  have hnormalizedZero :=
    probabilityMeasure_singleton_zero_eq_zero_of_uniform_quadratic_smallBall
      (fun j => (tail j).normalize) target.normalize hnormalizeTail
      normalizedConstant hnormalizedConstant_nonneg hnormalizedBound
  have hnormalizedZeroNN : target.normalize ({0} : Set Real) = 0 :=
    (ProbabilityMeasure.null_iff_toMeasure_null
      target.normalize ({0} : Set Real)).2 hnormalizedZero
  have hself := target.self_eq_mass_mul_normalize ({0} : Set Real)
  rw [hnormalizedZeroNN, mul_zero] at hself
  exact (FiniteMeasure.null_iff_toMeasure_null
    target ({0} : Set Real)).1 hself

end

end ArchonPhysics.FiniteMeasureQuadraticSmallBallWeakLimit

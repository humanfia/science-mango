import Mathlib.MeasureTheory.Measure.Portmanteau
import ArchonPhysics.FiniteMeasureVanishingErrorSmallBallWeakLimit

/-!
# L-infinity domination under finite-measure weak limits

An additive good/bad estimate

`mu_n A <= C * nu A + error_n`

for every measurable set, with `error_n -> 0`, passes to a finite weak limit
as the exact measure domination `mu <= C • nu`.  In particular the limit is
absolutely continuous with Radon--Nikodym density essentially bounded by
`C`.

The proof normalizes a nonzero finite limit and uses the probability
portmanteau inequality on open sets.  Convergence of total masses cancels the
normalization exactly, so there is no factor-of-two loss.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit

open Filter MeasureTheory Set

noncomputable section

/-- Uniform domination up to a vanishing scalar error is stable under weak
convergence of finite Borel measures. -/
theorem finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n) :
    (target : Measure X) ≤ C • reference := by
  by_cases htarget : target = 0
  · subst target
    exact bot_le
  have htargetMass : target.mass ≠ 0 :=
    target.mass_nonzero_iff.mpr htarget
  have htargetMass_pos : 0 < target.mass :=
    pos_iff_ne_zero.mpr htargetMass
  have hmass : Tendsto (fun n => (source n).mass) atTop
      (nhds target.mass) := hlimit.mass
  have hmassPositiveEventually :
      ∀ᶠ n in atTop, 0 < (source n).mass :=
    hmass.eventually (Ioi_mem_nhds htargetMass_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmassPositiveEventually
  let tail : Nat → FiniteMeasure X := fun j => source (j + N)
  have htailMass_pos (j : Nat) : 0 < (tail j).mass := by
    dsimp [tail]
    exact hN (j + N) (Nat.le_add_left N j)
  have htailNonzero (j : Nat) : tail j ≠ 0 :=
    (tail j).mass_nonzero_iff.mp (ne_of_gt (htailMass_pos j))
  have hnormalize : Tendsto (fun n => (source n).normalize) atTop
      (nhds target.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hlimit htarget
  have hnormalizeTail : Tendsto (fun j => (tail j).normalize) atTop
      (nhds target.normalize) := by
    change Tendsto
      ((fun n => (source n).normalize) ∘ (fun j : Nat => j + N))
      atTop (nhds target.normalize)
    exact hnormalize.comp (tendsto_add_atTop_nat N)
  have hmassTail : Tendsto (fun j => (tail j).mass) atTop
      (nhds target.mass) := by
    change Tendsto ((fun n => (source n).mass) ∘ (fun j : Nat => j + N))
      atTop (nhds target.mass)
    exact hmass.comp (tendsto_add_atTop_nat N)
  have hmassTailENN : Tendsto (fun j => ((tail j).mass : ENNReal)) atTop
      (nhds (target.mass : ENNReal)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hmassTail
  have htargetMassENN_ne : (target.mass : ENNReal) ≠ 0 := by
    exact_mod_cast htargetMass
  have htargetMassENN_ne_top : (target.mass : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hmassInv : Tendsto
      (fun j => ((tail j).mass : ENNReal)⁻¹) atTop
      (nhds ((target.mass : ENNReal)⁻¹)) :=
    tendsto_inv_iff.2 hmassTailENN
  have herrorTail : Tendsto (fun j => error (j + N)) atTop (nhds 0) :=
    herror.comp (tendsto_add_atTop_nat N)
  have hopenBound (G : Set X) (hG : IsOpen G) :
      (target : Measure X) G ≤ C * reference G := by
    by_cases hbaseTop : C * reference G = ∞
    · rw [hbaseTop]
      exact le_top
    let base : ENNReal := C * reference G
    let upper : Nat → ENNReal := fun j =>
      ((tail j).mass : ENNReal)⁻¹ * (base + error (j + N))
    have hbaseFinite : base ≠ ∞ := by
      exact hbaseTop
    have hadd : Tendsto (fun j => base + error (j + N)) atTop
        (nhds base) := by
      simpa using (tendsto_const_nhds.add herrorTail)
    have hinvFinite : (target.mass : ENNReal)⁻¹ ≠ ∞ := by
      rw [ENNReal.inv_ne_top]
      exact htargetMassENN_ne
    have hupper : Tendsto upper atTop
        (nhds ((target.mass : ENNReal)⁻¹ * base)) := by
      unfold upper
      exact ENNReal.Tendsto.mul hmassInv
        (Or.inl (ENNReal.inv_ne_zero.mpr htargetMassENN_ne_top)) hadd
        (Or.inr hinvFinite)
    have hnormalizedBound (j : Nat) :
        ((tail j).normalize : Measure X) G ≤ upper j := by
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
        (tail j) (htailNonzero j), Measure.smul_apply]
      rw [ENNReal.smul_def, ENNReal.coe_inv (ne_of_gt (htailMass_pos j))]
      change ((tail j).mass : ENNReal)⁻¹ *
          (tail j : Measure X) G ≤
        ((tail j).mass : ENNReal)⁻¹ *
          (base + error (j + N))
      apply mul_le_mul_right
      dsimp [tail, base]
      exact hbound (j + N) G hG.measurableSet
    have hopen :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        hnormalizeTail hG
    have hnormalizedTarget :
        (target.normalize : Measure X) G ≤
          (target.mass : ENNReal)⁻¹ * base := by
      calc
        (target.normalize : Measure X) G ≤
            atTop.liminf (fun j =>
              ((tail j).normalize : Measure X) G) := hopen
        _ ≤ atTop.liminf upper :=
          Filter.liminf_le_liminf
            (Eventually.of_forall hnormalizedBound)
        _ = (target.mass : ENNReal)⁻¹ * base :=
          hupper.liminf_eq
    have hselfENN : (target : Measure X) G =
        (target.mass : ENNReal) * (target.normalize : Measure X) G := by
      have hselfNN := target.self_eq_mass_mul_normalize G
      have hselfCoe := congrArg (fun x : NNReal => (x : ENNReal)) hselfNN
      simpa only [ENNReal.coe_mul,
        FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hselfCoe
    rw [hselfENN]
    calc
      (target.mass : ENNReal) * (target.normalize : Measure X) G ≤
          (target.mass : ENNReal) *
            ((target.mass : ENNReal)⁻¹ * base) :=
        mul_le_mul_right hnormalizedTarget _
      _ = base := by
        rw [← mul_assoc,
          ENNReal.mul_inv_cancel htargetMassENN_ne htargetMassENN_ne_top,
          one_mul]
      _ = C * reference G := rfl
  let _ : Measure.OuterRegular (C • reference) :=
    Measure.OuterRegular.smul reference hC
  apply Measure.le_iff.2
  intro A _hA
  rw [A.measure_eq_iInf_isOpen (C • reference)]
  refine le_iInf fun U => le_iInf fun hAU => le_iInf fun hU => ?_
  calc
    (target : Measure X) A ≤ (target : Measure X) U :=
      measure_mono hAU
    _ ≤ C * reference U := hopenBound U hU
    _ = (C • reference) U := by
      rw [Measure.smul_apply, smul_eq_mul]

/-- Consequently the weak limit is absolutely continuous with respect to the
reference measure. -/
theorem finiteMeasure_absolutelyContinuous_of_tendsto_of_apply_le_add_vanishingError
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (source n : Measure X) A ≤ C * reference A + error n) :
    (target : Measure X) ≪ reference := by
  exact (finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    source target hlimit reference C hC error herror hbound).absolutelyContinuous.trans
      Measure.smul_absolutelyContinuous

end

end ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit

import ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit

/-!
# L-infinity domination from eventual bounds on each fixed open set

Finite-volume empirical measures are atomic, so a domination estimate on
*all* measurable sets at each finite volume cannot have a vanishing additive
error unless their total mass vanishes: one may choose the finite atomic
support itself.  The weak-limit-compatible quantifier order is instead

`forall open G, eventually n, mu_n G <= C * reference G + error_n`.

Here `G` is fixed before the tail in `n` is selected.  Portmanteau then gives
the same sharp domination `mu <= C * reference` for the weak limit.  This is
the model-facing form suitable for atomic empirical approximants.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.FiniteMeasureEventualOpenLInfinityWeakLimit

open Filter MeasureTheory Set

noncomputable section

/-- Eventual domination on every fixed open set is stable under weak
convergence of finite Borel measures. -/
theorem finiteMeasure_le_smul_of_tendsto_of_eventually_isOpen_apply_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ G, IsOpen G → ∀ᶠ n in atTop,
      (source n : Measure X) G ≤ C * reference G + error n) :
    (target : Measure X) ≤ C • reference := by
  by_cases htarget : target = 0
  · subst target
    exact bot_le
  have htargetMass : target.mass ≠ 0 :=
    target.mass_nonzero_iff.mpr htarget
  have htargetMass_pos : 0 < target.mass :=
    pos_iff_ne_zero.mpr htargetMass
  have hmass : Tendsto (fun n ↦ (source n).mass) atTop
      (nhds target.mass) := hlimit.mass
  have hmassPositiveEventually :
      ∀ᶠ n in atTop, 0 < (source n).mass :=
    hmass.eventually (Ioi_mem_nhds htargetMass_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmassPositiveEventually
  let tail : Nat → FiniteMeasure X := fun j ↦ source (j + N)
  have htailMass_pos (j : Nat) : 0 < (tail j).mass := by
    dsimp [tail]
    exact hN (j + N) (Nat.le_add_left N j)
  have htailNonzero (j : Nat) : tail j ≠ 0 :=
    (tail j).mass_nonzero_iff.mp (ne_of_gt (htailMass_pos j))
  have hnormalize : Tendsto (fun n ↦ (source n).normalize) atTop
      (nhds target.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hlimit htarget
  have hnormalizeTail : Tendsto (fun j ↦ (tail j).normalize) atTop
      (nhds target.normalize) := by
    change Tendsto
      ((fun n ↦ (source n).normalize) ∘ (fun j : Nat ↦ j + N))
      atTop (nhds target.normalize)
    exact hnormalize.comp (tendsto_add_atTop_nat N)
  have hmassTail : Tendsto (fun j ↦ (tail j).mass) atTop
      (nhds target.mass) := by
    change Tendsto ((fun n ↦ (source n).mass) ∘ (fun j : Nat ↦ j + N))
      atTop (nhds target.mass)
    exact hmass.comp (tendsto_add_atTop_nat N)
  have hmassTailENN : Tendsto (fun j ↦ ((tail j).mass : ENNReal)) atTop
      (nhds (target.mass : ENNReal)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hmassTail
  have htargetMassENN_ne : (target.mass : ENNReal) ≠ 0 := by
    exact_mod_cast htargetMass
  have htargetMassENN_ne_top : (target.mass : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hmassInv : Tendsto
      (fun j ↦ ((tail j).mass : ENNReal)⁻¹) atTop
      (nhds ((target.mass : ENNReal)⁻¹)) :=
    tendsto_inv_iff.2 hmassTailENN
  have herrorTail : Tendsto (fun j ↦ error (j + N)) atTop (nhds 0) :=
    herror.comp (tendsto_add_atTop_nat N)
  have hopenBound (G : Set X) (hG : IsOpen G) :
      (target : Measure X) G ≤ C * reference G := by
    by_cases hbaseTop : C * reference G = ∞
    · rw [hbaseTop]
      exact le_top
    let base : ENNReal := C * reference G
    let upper : Nat → ENNReal := fun j ↦
      ((tail j).mass : ENNReal)⁻¹ * (base + error (j + N))
    have hbaseFinite : base ≠ ∞ := hbaseTop
    have hadd : Tendsto (fun j ↦ base + error (j + N)) atTop
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
    have hboundTail : ∀ᶠ j in atTop,
        (tail j : Measure X) G ≤ base + error (j + N) := by
      have h := (tendsto_add_atTop_nat N).eventually (hbound G hG)
      simpa only [tail, base, Function.comp_apply] using h
    have hnormalizedBound : ∀ᶠ j in atTop,
        ((tail j).normalize : Measure X) G ≤ upper j := by
      filter_upwards [hboundTail] with j hj
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
        (tail j) (htailNonzero j), Measure.smul_apply]
      rw [ENNReal.smul_def, ENNReal.coe_inv (ne_of_gt (htailMass_pos j))]
      change ((tail j).mass : ENNReal)⁻¹ *
          (tail j : Measure X) G ≤
        ((tail j).mass : ENNReal)⁻¹ *
          (base + error (j + N))
      exact mul_le_mul_right hj _
    have hopen :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        hnormalizeTail hG
    have hnormalizedTarget :
        (target.normalize : Measure X) G ≤
          (target.mass : ENNReal)⁻¹ * base := by
      calc
        (target.normalize : Measure X) G ≤
            atTop.liminf (fun j ↦
              ((tail j).normalize : Measure X) G) := hopen
        _ ≤ atTop.liminf upper :=
          Filter.liminf_le_liminf hnormalizedBound
        _ = (target.mass : ENNReal)⁻¹ * base :=
          hupper.liminf_eq
    have hselfENN : (target : Measure X) G =
        (target.mass : ENNReal) * (target.normalize : Measure X) G := by
      have hselfNN := target.self_eq_mass_mul_normalize G
      have hselfCoe := congrArg (fun x : NNReal ↦ (x : ENNReal)) hselfNN
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
  refine le_iInf fun U ↦ le_iInf fun hAU ↦ le_iInf fun hU ↦ ?_
  calc
    (target : Measure X) A ≤ (target : Measure X) U :=
      measure_mono hAU
    _ ≤ C * reference U := hopenBound U hU
    _ = (C • reference) U := by
      rw [Measure.smul_apply, smul_eq_mul]

/-- Eventual fixed-open-set domination gives forward absolute continuity of
the weak limit. -/
theorem finiteMeasure_absolutelyContinuous_of_tendsto_of_eventually_isOpen_apply_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ G, IsOpen G → ∀ᶠ n in atTop,
      (source n : Measure X) G ≤ C * reference G + error n) :
    (target : Measure X) ≪ reference := by
  have hle :=
    finiteMeasure_le_smul_of_tendsto_of_eventually_isOpen_apply_le
      source target hlimit reference C hC error herror hbound
  exact hle.absolutelyContinuous.trans Measure.smul_absolutelyContinuous

end

end ArchonPhysics.FiniteMeasureEventualOpenLInfinityWeakLimit

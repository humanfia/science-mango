import ArchonPhysics.AdditiveTriangleMeasureSupport
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Almost-everywhere additive rigidity on a compact interval

This module removes the continuity premise from restricted Cauchy rigidity.
An integrable profile satisfying the Cauchy equation Lebesgue-almost
everywhere on the additive triangle is linear almost everywhere.

The proof is constructive at the level of representatives.  It extends the
profile by zero, takes its continuous indefinite integral, and uses the
Cauchy equation integrated over a fixed interval to obtain continuous lower
and upper representatives.  The representatives agree on their overlap,
so they glue to a continuous profile.  Existing continuous restricted-Cauchy
rigidity then finishes the classification.

`IntegrableOn` is deliberately the only size premise.  In particular, a
measurable essentially bounded profile on `[0, W]`, such as a representative
of `Lp Real infinity`, satisfies it on this finite-measure interval.
-/

namespace ArchonPhysics.MeasurableIntervalAdditiveRigidity

open Set MeasureTheory
open ArchonPhysics.AdditiveTriangleMeasureSupport
open ArchonPhysics.ContinuousIntervalAdditiveRigidity
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity

noncomputable section

/-- An integrable profile which is additive almost everywhere on the positive
triangle is a scalar multiple of frequency almost everywhere on the compact
interval.  No continuity of the original representative is assumed. -/
theorem integrable_interval_ae_additive_linear
    {profile : Real -> Real} {W : Real} (hW : 0 < W)
    (hprofile : IntegrableOn profile (Icc (0 : Real) W))
    (hbalance :
      ∀ᵐ pair ∂(volume.restrict (additiveFrequencyTriangle W)),
        profile (pair.1 + pair.2) = profile pair.1 + profile pair.2) :
    ∃ beta : Real,
      ∀ᵐ omega ∂volume.restrict (Icc (0 : Real) W),
        profile omega = beta * omega := by
  let t : Real := W / 3
  let m : Real := W / 2
  let compactProfile : Real -> Real :=
    (Icc (0 : Real) W).indicator profile
  have hcompact : Integrable compactProfile volume := by
    exact (integrable_indicator_iff measurableSet_Icc).2 hprofile
  let primitive : Real -> Real := fun x =>
    ∫ z in (0 : Real)..x, compactProfile z
  have hprimitive : Continuous primitive := by
    exact hcompact.continuous_primitive 0
  let low : Real -> Real := fun x =>
    (primitive (x + t) - primitive x - primitive t) / t
  let high : Real -> Real := fun x =>
    (primitive x - primitive (x - t) + primitive t) / t
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have htW : t < W := by
    dsimp [t]
    linarith
  have hm : t < m := by
    dsimp [t, m]
    linarith
  have hm' : m < W - t := by
    dsimp [t, m]
    linarith
  have hlow : Continuous low := by
    dsimp [low]
    fun_prop
  have hhigh : Continuous high := by
    dsimp [high]
    fun_prop
  have hbalanceGlobal :
      ∀ᵐ pair ∂(volume : Measure (Real × Real)),
        pair ∈ additiveFrequencyTriangle W ->
          profile (pair.1 + pair.2) = profile pair.1 + profile pair.2 :=
    (ae_restrict_iff'
      (isClosed_additiveFrequencyTriangle W).measurableSet).1 hbalance
  rw [Measure.volume_eq_prod] at hbalanceGlobal
  have hbalanceSlices :
      ∀ᵐ x ∂(volume : Measure Real), ∀ᵐ y ∂(volume : Measure Real),
        (x, y) ∈ additiveFrequencyTriangle W ->
          profile (x + y) = profile x + profile y :=
    Measure.ae_ae_of_ae_prod hbalanceGlobal
  have hbalanceParentSlices :
      ∀ᵐ x ∂(volume : Measure Real), ∀ᵐ y ∂(volume : Measure Real),
        (x - y, y) ∈ additiveFrequencyTriangle W ->
          profile ((x - y) + y) = profile (x - y) + profile y := by
    have hshear := (measurePreserving_sub_prod
      (volume : Measure Real) (volume : Measure Real)).quasiMeasurePreserving.ae
        hbalanceGlobal
    exact Measure.ae_ae_of_ae_prod hshear
  have hcompact_eq :
      ∀ x, x ∈ Icc (0 : Real) W -> compactProfile x = profile x := by
    intro x hx
    simp [compactProfile, hx]
  have hcompact_interval : IntervalIntegrable compactProfile volume 0 W :=
    hcompact.intervalIntegrable
  have hlowAEGlobal :
      ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (0 : Real) (W - t) -> low x = profile x := by
    filter_upwards [hbalanceSlices] with x hx
    intro hxrange
    have hxt : x + t <= W := by linarith [hxrange.2]
    have hxt0 : 0 <= x + t := by linarith [hxrange.1, ht]
    have hxW : x <= W := hxrange.2.trans (sub_le_self W ht.le)
    have hInt0x : IntervalIntegrable compactProfile volume 0 x :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le, uIcc_of_le hxrange.1]
        exact Icc_subset_Icc_right hxW)
    have hIntxxt : IntervalIntegrable compactProfile volume x (x + t) :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le, uIcc_of_le (by linarith : x <= x + t)]
        exact Icc_subset_Icc hxrange.1 hxt)
    have hInt0t : IntervalIntegrable compactProfile volume 0 t :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le, uIcc_of_le ht.le]
        exact Icc_subset_Icc_right htW.le)
    have hIntegralBalance :
        (∫ y in (0 : Real)..t, compactProfile (x + y)) =
          ∫ y in (0 : Real)..t, profile x + compactProfile y := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hx] with y hy
      intro hyInterval
      have hyt : y ∈ Ioc (0 : Real) t := by
        simpa [uIoc_of_le ht.le] using hyInterval
      have hyW : y <= W := hyt.2.trans htW.le
      have hxyW : x + y <= W := by
        linarith [hxrange.2, hyt.2]
      calc
        compactProfile (x + y) = profile (x + y) :=
          hcompact_eq _ ⟨by linarith [hxrange.1, hyt.1.le], hxyW⟩
        _ = profile x + profile y :=
          hy ⟨hxrange.1, hyt.1.le, hxyW⟩
        _ = profile x + compactProfile y := by
          rw [hcompact_eq _ ⟨hyt.1.le, hyW⟩]
    have hPrimitiveStep : primitive (x + t) - primitive x =
        ∫ y in (0 : Real)..t, compactProfile (x + y) := by
      have hadj :=
        intervalIntegral.integral_add_adjacent_intervals hInt0x hIntxxt
      rw [show (∫ y in (0 : Real)..t, compactProfile (x + y)) =
          ∫ z in x..x + t, compactProfile z by
        simpa only [zero_add, add_zero, add_comm] using
          (intervalIntegral.integral_comp_add_right compactProfile x
            (a := (0 : Real)) (b := t))]
      dsimp [primitive]
      linarith
    have hsum :
        (∫ y in (0 : Real)..t, profile x + compactProfile y) =
          t * profile x + primitive t := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hInt0t]
      simp [primitive, mul_comm]
    dsimp [low]
    rw [hPrimitiveStep, hIntegralBalance, hsum]
    field_simp
    ring
  have hlowAE :
      low =ᵐ[volume.restrict (Icc (0 : Real) (W - t))] profile := by
    exact (ae_restrict_iff' measurableSet_Icc).2 hlowAEGlobal
  have hhighAEGlobal :
      ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc t W -> high x = profile x := by
    filter_upwards [hbalanceParentSlices] with x hx
    intro hxrange
    have hxt0 : 0 <= x - t := by linarith [hxrange.1]
    have hInt0t : IntervalIntegrable compactProfile volume 0 t :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le, uIcc_of_le ht.le]
        exact Icc_subset_Icc_right htW.le)
    have hInt0sub : IntervalIntegrable compactProfile volume 0 (x - t) :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le, uIcc_of_le hxt0]
        exact Icc_subset_Icc_right (by linarith [hxrange.2, ht]))
    have hIntsubx : IntervalIntegrable compactProfile volume (x - t) x :=
      hcompact_interval.mono_set (by
        rw [uIcc_of_le hW.le,
          uIcc_of_le (by linarith : x - t <= x)]
        exact Icc_subset_Icc hxt0 hxrange.2)
    have hIntegralBalance :
        (∫ y in (0 : Real)..t,
          compactProfile (x - y) + compactProfile y) =
          ∫ _y in (0 : Real)..t, profile x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hx] with y hy
      intro hyInterval
      have hyt : y ∈ Ioc (0 : Real) t := by
        simpa [uIoc_of_le ht.le] using hyInterval
      have hsub : x - y ∈ Icc (0 : Real) W := by
        constructor <;>
          linarith [hxrange.1, hxrange.2, hyt.1.le, hyt.2]
      have hyW : y <= W := hyt.2.trans htW.le
      calc
        compactProfile (x - y) + compactProfile y =
            profile (x - y) + profile y := by
          rw [hcompact_eq _ hsub, hcompact_eq _ ⟨hyt.1.le, hyW⟩]
        _ = profile ((x - y) + y) :=
          (hy ⟨hsub.1, hyt.1.le, by simpa using hxrange.2⟩).symm
        _ = profile x := by ring_nf
    have hPrimitiveStep : primitive x - primitive (x - t) =
        ∫ y in (0 : Real)..t, compactProfile (x - y) := by
      have hadj :=
        intervalIntegral.integral_add_adjacent_intervals hInt0sub hIntsubx
      have hshift : (∫ y in (0 : Real)..t, compactProfile (x - y)) =
          ∫ z in x - t..x, compactProfile z := by
        simpa only [sub_zero] using
          (intervalIntegral.integral_comp_sub_left compactProfile x
            (a := (0 : Real)) (b := t))
      rw [hshift]
      dsimp [primitive]
      linarith
    have hsum :
        (∫ y in (0 : Real)..t,
          compactProfile (x - y) + compactProfile y) =
          (primitive x - primitive (x - t)) + primitive t := by
      have hshiftInt :
          IntervalIntegrable (fun y => compactProfile (x - y)) volume 0 t := by
        simpa using (hIntsubx.comp_sub_left x).symm
      rw [intervalIntegral.integral_add hshiftInt hInt0t, hPrimitiveStep]
    dsimp [high]
    rw [← hsum, hIntegralBalance]
    simp [ht.ne', mul_comm]
  have hhighAE :
      high =ᵐ[volume.restrict (Icc t W)] profile := by
    exact (ae_restrict_iff' measurableSet_Icc).2 hhighAEGlobal
  have hoverlapLow : Ioo t (W - t) ⊆ Icc (0 : Real) (W - t) := by
    intro x hx
    exact ⟨ht.le.trans hx.1.le, hx.2.le⟩
  have hoverlapHigh : Ioo t (W - t) ⊆ Icc t W := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le.trans (sub_le_self W ht.le)⟩
  have hlowHighAE :
      low =ᵐ[volume.restrict (Ioo t (W - t))] high := by
    have hl := ae_restrict_of_ae_restrict_of_subset hoverlapLow hlowAE
    have hh := ae_restrict_of_ae_restrict_of_subset hoverlapHigh hhighAE
    filter_upwards [hl, hh] with x hxl hxh
    exact hxl.trans hxh.symm
  have hlowHighOn : Set.EqOn low high (Ioo t (W - t)) :=
    Measure.eqOn_open_of_ae_eq hlowHighAE isOpen_Ioo
      hlow.continuousOn hhigh.continuousOn
  have hboundary : low m = high m := hlowHighOn ⟨hm, hm'⟩
  let regularProfile : Real -> Real := fun x =>
    if x <= m then low x else high x
  have hregular : Continuous regularProfile := by
    dsimp [regularProfile]
    exact continuous_if_le continuous_id continuous_const
      hlow.continuousOn hhigh.continuousOn (by
        intro x hx
        simpa [hx] using hboundary)
  have hregularAEGlobal :
      ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (0 : Real) W -> regularProfile x = profile x := by
    filter_upwards [hlowAEGlobal, hhighAEGlobal] with x hxlow hxhigh
    intro hxrange
    by_cases hxm : x <= m
    · have hxsmall : x ∈ Icc (0 : Real) (W - t) :=
        ⟨hxrange.1, hxm.trans hm'.le⟩
      simpa [regularProfile, hxm] using hxlow hxsmall
    · have hxlarge : x ∈ Icc t W :=
        ⟨hm.le.trans (le_of_not_ge hxm), hxrange.2⟩
      simpa [regularProfile, hxm] using hxhigh hxlarge
  have hregularAE :
      regularProfile =ᵐ[volume.restrict (Icc (0 : Real) W)] profile :=
    (ae_restrict_iff' measurableSet_Icc).2 hregularAEGlobal
  have hregularBalance :
      ∀ᵐ pair ∂volume.restrict (additiveFrequencyTriangle W),
        regularProfile (pair.1 + pair.2) =
          regularProfile pair.1 + regularProfile pair.2 := by
    have hfirst := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure Real))
      (ν := (volume : Measure Real))).ae hregularAEGlobal
    have hsecond := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure Real))
      (ν := (volume : Measure Real))).ae hregularAEGlobal
    have hsumQMP : Measure.QuasiMeasurePreserving
        (fun pair : Real × Real => pair.1 + pair.2)
        ((volume : Measure Real).prod volume) volume := by
      simpa [Function.comp_def] using
        (Measure.quasiMeasurePreserving_fst
          (μ := (volume : Measure Real))
          (ν := (volume : Measure Real))).comp
          (measurePreserving_add_prod
            (volume : Measure Real)
            (volume : Measure Real)).quasiMeasurePreserving
    have hsum := hsumQMP.ae hregularAEGlobal
    have hbal := hbalanceGlobal
    have hall :
        ∀ᵐ pair ∂((volume : Measure Real).prod volume),
          pair ∈ additiveFrequencyTriangle W ->
            regularProfile (pair.1 + pair.2) =
              regularProfile pair.1 + regularProfile pair.2 := by
      filter_upwards [hfirst, hsecond, hsum, hbal] with pair h1 h2 hs hb
      intro hpair
      have hfst : pair.1 ∈ Icc (0 : Real) W :=
        ⟨hpair.1,
          (le_add_of_nonneg_right hpair.2.1).trans hpair.2.2⟩
      have hsnd : pair.2 ∈ Icc (0 : Real) W :=
        ⟨hpair.2.1,
          (le_add_of_nonneg_left hpair.1).trans hpair.2.2⟩
      have hadd : pair.1 + pair.2 ∈ Icc (0 : Real) W :=
        ⟨add_nonneg hpair.1 hpair.2.1, hpair.2.2⟩
      rw [hs hadd, h1 hfst, h2 hsnd]
      exact hb hpair
    rw [← Measure.volume_eq_prod] at hall
    exact (ae_restrict_iff'
      (isClosed_additiveFrequencyTriangle W).measurableSet).2 hall
  have hregularPointwise :=
    continuousOn_frequencyBalance_of_ae_restrict_of_fullSupport
      hregular.continuousOn
      (additiveFrequencyTriangle_subset_volume_restrict_support hW)
      hregularBalance
  have hadd : forall x, x ∈ Icc (0 : Real) W ->
      forall y, y ∈ Icc (0 : Real) W -> x + y <= W ->
        regularProfile (x + y) = regularProfile x + regularProfile y := by
    intro x hx y hy hxy
    exact hregularPointwise (x, y) ⟨hx.1, hy.1, hxy⟩
  obtain ⟨beta, hbeta⟩ :=
    continuousOn_interval_additive_linear regularProfile hW
      hregular.continuousOn hadd
  refine ⟨beta, ?_⟩
  filter_upwards [hregularAE, ae_restrict_mem measurableSet_Icc] with
    x hx hxmem
  rw [← hx, hbeta x hxmem]

end

end ArchonPhysics.MeasurableIntervalAdditiveRigidity

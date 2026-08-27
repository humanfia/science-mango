import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian

/-!
# Bounded differences on a finite product probability space

This module proves the finite-product bounded-differences-to-sub-Gaussian
bridge needed for McDiarmid concentration.  The proof is internal: it splits
off the first coordinate, applies Mathlib's Hoeffding lemma to its centered
section average, applies the induction hypothesis to the remaining product,
and combines the two moment-generating-function bounds by Fubini.

No independence or conditional-moment theorem is postulated.  Independence
is represented by the actual finite product measure `Measure.pi`.
-/

namespace ArchonPhysics.FiniteProductBoundedDifferences

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Coordinatewise bounded differences for functions on a `Fin n` product. -/
def HasFinBoundedDifferences
    {alpha : Type*} {n : Nat} (f : (Fin n -> alpha) -> Real)
    (c : Fin n -> NNReal) : Prop :=
  forall x y i, (forall j, j ≠ i -> x j = y j) ->
    |f x - f y| <= (c i : Real)

/-- The sub-Gaussian variance proxy furnished by bounded differences. -/
def varianceProxy {n : Nat} (c : Fin n -> NNReal) : NNReal :=
  ∑ i, (c i / 2) ^ 2

lemma hasSubgaussianMGF_mono_parameter
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : Omega -> Real} {c d : NNReal}
    (h : HasSubgaussianMGF X c mu) (hcd : c <= d) :
    HasSubgaussianMGF X d mu where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := h.mgf_le t |>.trans <| Real.exp_le_exp.mpr <| by
    gcongr

/-- Hoeffding's lemma with the sharp diameter bound, without requiring
attainment of an infimum or supremum. -/
lemma hasSubgaussianMGF_of_pairwise_bounded
    {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]
    {mu : Measure alpha} [IsProbabilityMeasure mu]
    {g : alpha -> Real} {c : NNReal}
    (hg : Measurable g)
    (hpair : forall x y, |g x - g y| <= (c : Real)) :
    HasSubgaussianMGF (fun x => g x - (∫ y, g y ∂mu))
      ((c / 2) ^ 2) mu := by
  let anchor : alpha := Classical.choice ‹Nonempty alpha›
  let lower : Real := sInf (Set.range g)
  let upper : Real := sSup (Set.range g)
  have hrange_nonempty : (Set.range g).Nonempty := Set.range_nonempty g
  have hbddBelow : BddBelow (Set.range g) := by
    refine ⟨g anchor - (c : Real), ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [(abs_le.mp (hpair x anchor)).1]
  have hbddAbove : BddAbove (Set.range g) := by
    refine ⟨g anchor + (c : Real), ?_⟩
    rintro _ ⟨x, rfl⟩
    linarith [(abs_le.mp (hpair x anchor)).2]
  have hlower (x : alpha) : lower <= g x := by
    exact csInf_le hbddBelow ⟨x, rfl⟩
  have hupper (x : alpha) : g x <= upper := by
    exact le_csSup hbddAbove ⟨x, rfl⟩
  have hlower_le_upper : lower <= upper :=
    (hlower anchor).trans (hupper anchor)
  have hwidth : upper - lower <= (c : Real) := by
    have hx (x : alpha) : g x <= lower + (c : Real) := by
      have hxc : g x - (c : Real) <= lower := by
        apply le_csInf hrange_nonempty
        rintro _ ⟨y, rfl⟩
        have := (abs_le.mp (hpair x y)).2
        linarith
      linarith
    have := csSup_le hrange_nonempty (by
      rintro _ ⟨x, rfl⟩
      exact hx x)
    linarith
  have hbase : HasSubgaussianMGF
      (fun x => g x - (∫ y, g y ∂mu))
      ((‖upper - lower‖₊ / 2) ^ 2) mu := by
    apply hasSubgaussianMGF_of_mem_Icc hg.aemeasurable
    exact ae_of_all _ fun x => ⟨hlower x, hupper x⟩
  apply hasSubgaussianMGF_mono_parameter hbase
  change (((‖upper - lower‖₊ / 2) ^ 2 : NNReal) : Real) <=
    (((c / 2) ^ 2 : NNReal) : Real)
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm]
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlower_le_upper)]
  nlinarith [NNReal.coe_nonneg c]

/-- Combine a sub-Gaussian first-coordinate term with sectionwise
sub-Gaussian remainder terms under a product measure. -/
lemma hasSubgaussianMGF_add_prod_of_forall
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {mu : Measure alpha} {nu : Measure beta}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {A : alpha -> Real} {B : alpha -> beta -> Real} {cA cB : NNReal}
    (hA : HasSubgaussianMGF A cA mu)
    (hB : forall a, HasSubgaussianMGF (B a) cB nu)
    (hExp : forall t, Integrable
      (fun p : alpha × beta => Real.exp (t * (A p.1 + B p.1 p.2)))
      (mu.prod nu)) :
    HasSubgaussianMGF
      (fun p : alpha × beta => A p.1 + B p.1 p.2)
      (cA + cB) (mu.prod nu) where
  integrable_exp_mul := hExp
  mgf_le t := by
    have hfull := hExp t
    have hleft : Integrable
        (fun a => Real.exp (t * A a) * mgf (B a) nu t) mu := by
      simpa only [mgf, mul_add, Real.exp_add, integral_const_mul] using
        hfull.integral_prod_left
    have hright : Integrable
        (fun a => Real.exp (t * A a) * Real.exp ((cB : Real) * t ^ 2 / 2)) mu :=
      (hA.integrable_exp_mul t).mul_const _
    rw [mgf, integral_prod _ hfull]
    simp_rw [mul_add, Real.exp_add, integral_const_mul]
    calc
      (∫ a, Real.exp (t * A a) * mgf (B a) nu t ∂mu) <=
          ∫ a, Real.exp (t * A a) * Real.exp ((cB : Real) * t ^ 2 / 2) ∂mu := by
        apply integral_mono hleft hright
        intro a
        exact mul_le_mul_of_nonneg_left ((hB a).mgf_le t) (Real.exp_nonneg _)
      _ = mgf A mu t * Real.exp ((cB : Real) * t ^ 2 / 2) := by
        rw [integral_mul_const]
        rfl
      _ <= Real.exp ((cA : Real) * t ^ 2 / 2) *
          Real.exp ((cB : Real) * t ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_right (hA.mgf_le t) (Real.exp_nonneg _)
      _ = Real.exp (((cA + cB : NNReal) : Real) * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        simp only [NNReal.coe_add]
        congr 1
        ring

/-- McDiarmid's bounded-differences MGF estimate on a genuine finite
product probability measure.  The `[0,1]` hypothesis is used only to obtain
integrability uniformly during the finite induction. -/
theorem hasSubgaussianMGF_finitePi_of_boundedDifferences
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (n : Nat) (f : (Fin n -> alpha) -> Real) (c : Fin n -> NNReal)
    (hf : Measurable f)
    (hrange : forall x, f x ∈ Set.Icc 0 1)
    (hbounded : HasFinBoundedDifferences f c) :
    HasSubgaussianMGF
      (fun x => f x - (∫ y, f y ∂(Measure.pi fun _ : Fin n => mu)))
      (varianceProxy c) (Measure.pi fun _ : Fin n => mu) := by
  induction n with
  | zero =>
      let x0 : Fin 0 -> alpha := fun i => Fin.elim0 i
      have hconst : f = fun _ => f x0 := by
        funext x
        congr 1
        exact Subsingleton.elim x x0
      rw [hconst]
      simp [varianceProxy]
  | succ n ih =>
      let tailMeasure : Measure (Fin n -> alpha) :=
        Measure.pi fun _ : Fin n => mu
      let splitEquiv : (Fin (n + 1) -> alpha) ≃ᵐ
          alpha × (Fin n -> alpha) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => alpha) 0
      let F : alpha × (Fin n -> alpha) -> Real :=
        fun p => f (Fin.cons p.1 p.2)
      have hF : Measurable F := by
        have hcomp : Measurable (f ∘ splitEquiv.symm) :=
          hf.comp splitEquiv.symm.measurable
        simpa [F, splitEquiv, Function.comp_def,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero] using hcomp
      have hF_range (p : alpha × (Fin n -> alpha)) : F p ∈ Set.Icc 0 1 := by
        exact hrange (Fin.cons p.1 p.2)
      have hF_integrable : Integrable F (mu.prod tailMeasure) :=
        Integrable.of_mem_Icc 0 1 hF.aemeasurable
          (ae_of_all _ hF_range)
      have hF_section_integrable (a : alpha) :
          Integrable (fun y => F (a, y)) tailMeasure := by
        apply Integrable.of_mem_Icc 0 1
        · exact (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
        · exact ae_of_all _ fun y => hF_range (a, y)
      let g : alpha -> Real := fun a => ∫ y, F (a, y) ∂tailMeasure
      have hg : Measurable g := by
        exact hF.stronglyMeasurable.integral_prod_right.measurable
      have hg_range (a : alpha) : g a ∈ Set.Icc 0 1 := by
        constructor
        · apply integral_nonneg_of_ae
          exact ae_of_all _ fun y => (hF_range (a, y)).1
        · calc
            (∫ y, F (a, y) ∂tailMeasure) <=
                ∫ _ : Fin n -> alpha, (1 : Real) ∂tailMeasure := by
              apply integral_mono (hF_section_integrable a) (integrable_const 1)
              intro y
              exact (hF_range (a, y)).2
            _ = 1 := by simp
      have hF_first_coordinate (a a' : alpha) (y : Fin n -> alpha) :
          |F (a, y) - F (a', y)| <= (c 0 : Real) := by
        apply hbounded (Fin.cons a y) (Fin.cons a' y) 0
        intro j hj
        exact Fin.cases (fun hj0 => (hj0 rfl).elim)
          (fun _ _ => by simp) j hj
      have hg_pairwise (a a' : alpha) :
          |g a - g a'| <= (c 0 : Real) := by
        rw [show g a - g a' =
            ∫ y, (F (a, y) - F (a', y)) ∂tailMeasure by
          rw [integral_sub (hF_section_integrable a) (hF_section_integrable a')]]
        have hnorm := norm_integral_le_of_norm_le_const
          (μ := tailMeasure)
          (f := fun y => F (a, y) - F (a', y))
          (C := (c 0 : Real))
          (ae_of_all _ fun y => hF_first_coordinate a a' y)
        simpa [Real.norm_eq_abs] using hnorm
      let A : alpha -> Real :=
        fun a => g a - (∫ z, g z ∂mu)
      let B : alpha -> (Fin n -> alpha) -> Real :=
        fun a y => F (a, y) - g a
      have hA : HasSubgaussianMGF A ((c 0 / 2) ^ 2) mu := by
        let _ : Nonempty alpha := nonempty_of_isProbabilityMeasure mu
        exact hasSubgaussianMGF_of_pairwise_bounded hg hg_pairwise
      have hB (a : alpha) :
          HasSubgaussianMGF (B a)
            (varianceProxy fun i : Fin n => c i.succ) tailMeasure := by
        apply ih (fun y => F (a, y)) (fun i : Fin n => c i.succ)
        · exact hF.comp (measurable_const.prodMk measurable_id)
        · exact fun y => hF_range (a, y)
        · intro x y i hoff
          apply hbounded (Fin.cons a x) (Fin.cons a y) i.succ
          intro j hj
          exact Fin.cases (fun _ => by simp)
            (fun k hjk => by
              simp only [Fin.cons_succ]
              apply hoff k
              intro hki
              apply hjk
              simp [hki]) j hj
      have hmean :
          (∫ a, g a ∂mu) = ∫ p, F p ∂(mu.prod tailMeasure) := by
        exact (integral_prod F hF_integrable).symm
      have htotal (p : alpha × (Fin n -> alpha)) :
          A p.1 + B p.1 p.2 =
            F p - (∫ z, F z ∂(mu.prod tailMeasure)) := by
        simp only [A, B]
        rw [hmean]
        ring
      have hmean_range :
          (∫ z, F z ∂(mu.prod tailMeasure)) ∈ Set.Icc 0 1 := by
        constructor
        · apply integral_nonneg_of_ae
          exact ae_of_all _ fun p => (hF_range p).1
        · calc
            (∫ z, F z ∂(mu.prod tailMeasure)) <=
                ∫ _ : alpha × (Fin n -> alpha), (1 : Real)
                  ∂(mu.prod tailMeasure) := by
              apply integral_mono hF_integrable (integrable_const 1)
              intro p
              exact (hF_range p).2
            _ = 1 := by simp
      have hExp (t : Real) : Integrable
          (fun p : alpha × (Fin n -> alpha) =>
            Real.exp (t * (A p.1 + B p.1 p.2)))
          (mu.prod tailMeasure) := by
        rw [show (fun p : alpha × (Fin n -> alpha) =>
              Real.exp (t * (A p.1 + B p.1 p.2))) =
            fun p => Real.exp
              (t * (F p - (∫ z, F z ∂(mu.prod tailMeasure)))) by
          funext p
          rw [htotal]]
        apply integrable_exp_mul_of_mem_Icc (a := -1) (b := 1)
          (hF.sub_const _).aemeasurable
        exact ae_of_all _ fun p => by
          constructor <;> linarith [(hF_range p).1, (hF_range p).2,
            hmean_range.1, hmean_range.2]
      have hprod := hasSubgaussianMGF_add_prod_of_forall hA hB hExp
      have hprod_centered : HasSubgaussianMGF
          (fun p => F p - (∫ z, F z ∂(mu.prod tailMeasure)))
          (((c 0 / 2) ^ 2) + varianceProxy (fun i : Fin n => c i.succ))
          (mu.prod tailMeasure) := by
        apply hprod.congr
        exact ae_of_all _ htotal
      have hsplit : MeasurePreserving splitEquiv
          (Measure.pi fun _ : Fin (n + 1) => mu)
          (mu.prod tailMeasure) := by
        exact measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => mu) 0
      have hmean_transport :
          (∫ x, f x ∂(Measure.pi fun _ : Fin (n + 1) => mu)) =
            ∫ p, F p ∂(mu.prod tailMeasure) := by
        simpa [F, splitEquiv,
          MeasurableEquiv.piFinSuccAbove_apply] using
          hsplit.integral_comp'
            (fun p => F p)
      have hprod_map : HasSubgaussianMGF
          (fun p => F p - (∫ z, F z ∂(mu.prod tailMeasure)))
          (((c 0 / 2) ^ 2) + varianceProxy (fun i : Fin n => c i.succ))
          ((Measure.pi fun _ : Fin (n + 1) => mu).map splitEquiv) := by
        rw [hsplit.map_eq]
        exact hprod_centered
      have htransport := HasSubgaussianMGF.of_map
        splitEquiv.measurable.aemeasurable hprod_map
      simpa [varianceProxy, Fin.sum_univ_succ, F, splitEquiv,
        Function.comp_def, hmean_transport,
        MeasurableEquiv.piFinSuccAbove_apply] using htransport

end

end ArchonPhysics.FiniteProductBoundedDifferences

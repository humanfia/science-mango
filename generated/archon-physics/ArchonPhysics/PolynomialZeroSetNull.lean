import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Lebesgue-null zero sets of real multivariate polynomials

This module packages the finite-dimensional fact needed by the random-lattice
grounding: a nonzero real polynomial vanishes only on a Lebesgue-null set.
The proof is by induction on the number of variables.  At the induction step,
`MvPolynomial.finSuccEquiv` exposes the first variable, the exceptional tails
are the zero set of its nonzero leading coefficient, and every other slice is
contained in the finite root set of a nonzero univariate polynomial.
-/

open MeasureTheory Set

namespace ArchonPhysics

open MvPolynomial

/-- A nonzero real multivariate polynomial in `n` variables has a
Lebesgue-null zero set. -/
theorem volume_zeroSet_mvPolynomial_eval :
    ∀ {n : ℕ} (P : MvPolynomial (Fin n) ℝ), P ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x P = 0} = 0
  | 0, P, hP => by
      rw [P.eq_C_of_isEmpty] at *
      simp [C_ne_zero.mp hP]
  | n + 1, P, hP => by
      let q : Polynomial (MvPolynomial (Fin n) ℝ) := finSuccEquiv ℝ n P
      let L : MvPolynomial (Fin n) ℝ := q.leadingCoeff
      have hq : q ≠ 0 := by
        exact EmbeddingLike.map_ne_zero_iff.mpr hP
      have hL : L ≠ 0 := by
        simpa [L] using Polynomial.leadingCoeff_ne_zero.mpr hq
      have hExceptional :
          volume {x : Fin n → ℝ | MvPolynomial.eval x L = 0} = 0 :=
        volume_zeroSet_mvPolynomial_eval L hL
      have hGood : ∀ᵐ x : Fin n → ℝ ∂volume, MvPolynomial.eval x L ≠ 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hExceptional] with x hx
        simpa only [Set.mem_ofPred_eq] using hx
      let S : Set (ℝ × (Fin n → ℝ)) :=
        {z | MvPolynomial.eval (Fin.cons z.1 z.2) P = 0}
      have hS : MeasurableSet S := by
        apply (isClosed_singleton.preimage ?_).measurableSet
        exact P.continuous_eval.comp <|
          continuous_pi fun i =>
            Fin.cases continuous_fst
              (fun j => (continuous_apply j).comp continuous_snd) i
      have hSlices :
          ∀ᵐ x : Fin n → ℝ ∂volume,
            volume ((fun y : ℝ => (y, x)) ⁻¹' S) = 0 := by
        filter_upwards [hGood] with x hx
        let px : Polynomial ℝ := q.map (MvPolynomial.eval x)
        have hpxLeading : px.leadingCoeff = MvPolynomial.eval x L := by
          simpa [px, L] using
            Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (MvPolynomial.eval x) hx
        have hpx : px ≠ 0 := by
          intro hzero
          have : px.leadingCoeff = 0 := by simp [hzero]
          exact hx (hpxLeading ▸ this)
        apply Set.Finite.measure_zero _ volume
        apply px.roots.finite_toSet.subset
        intro y hy
        change y ∈ px.roots
        rw [Polynomial.mem_roots hpx, Polynomial.IsRoot]
        have hEval : MvPolynomial.eval (Fin.cons y x) P = 0 := hy
        rw [MvPolynomial.eval_eq_eval_mv_eval'] at hEval
        simpa [px, q] using hEval
      have hSzero : volume S = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
        calc
          (∫⁻ x : Fin n → ℝ, volume ((fun y : ℝ => (y, x)) ⁻¹' S) ∂volume) =
              ∫⁻ _x : Fin n → ℝ, 0 ∂volume := lintegral_congr_ae hSlices
          _ = 0 := lintegral_zero
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have he : MeasurePreserving e :=
        volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      calc
        volume {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0} =
            volume (e ⁻¹' S) := by
              congr 1
              ext x
              simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, e]
              rw [MeasurableEquiv.piFinSuccAbove_apply]
              have hcoords :
                  Fin.cons ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0).symm x).1
                    ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) 0).symm x).2 = x := by
                ext i
                refine Fin.cases (by simp) (fun j => ?_) i
                rfl
              rw [hcoords]
        _ = volume S := he.measure_preimage hS.nullMeasurableSet
        _ = 0 := hSzero

end ArchonPhysics

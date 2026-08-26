import Mathlib.MeasureTheory.Function.Jacobian
import ArchonPhysics.FiniteMassPolynomialAvoidance

/-!
# Polynomial avoidance after coordinatewise inversion

Coordinatewise inversion is a smooth involution away from the coordinate
hyperplanes.  Those hyperplanes are themselves Lebesgue-null.  Consequently
the inverse image under coordinatewise inversion of the zero set of a
nonzero multivariate polynomial is again Lebesgue-null.  Absolute continuity
of the finite iid mass law then gives the corresponding almost-sure result.
-/

namespace ArchonPhysics

open MeasureTheory Set

noncomputable section

/-- Invert every real coordinate.  In Lean, `0⁻¹ = 0`, so this is a global
involution even though it is differentiable only off the coordinate
hyperplanes. -/
def coordinatewiseInv {N : Nat} (x : Fin N → Real) : Fin N → Real :=
  fun i ↦ (x i)⁻¹

@[simp] theorem coordinatewiseInv_apply {N : Nat} (x : Fin N → Real)
    (i : Fin N) : coordinatewiseInv x i = (x i)⁻¹ := rfl

@[simp] theorem coordinatewiseInv_involutive {N : Nat} (x : Fin N → Real) :
    coordinatewiseInv (coordinatewiseInv x) = x := by
  ext i
  simp [coordinatewiseInv]

/-- The open locus on which every coordinate is nonzero. -/
def allCoordinatesNonzero {N : Nat} : Set (Fin N → Real) :=
  {x | ∀ i, x i ≠ 0}

theorem differentiableOn_coordinatewiseInv {N : Nat} :
    DifferentiableOn Real coordinatewiseInv (allCoordinatesNonzero (N := N)) := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  rw [differentiableAt_pi]
  intro i
  exact (differentiableAt_apply i x).inv (hx i)

/-- The union of the coordinate hyperplanes has zero product Lebesgue
measure. -/
theorem volume_compl_allCoordinatesNonzero_eq_zero {N : Nat} :
    (volume : Measure (Fin N → Real))
        (allCoordinatesNonzero (N := N))ᶜ = 0 := by
  have hhyperplane (i : Fin N) :
      (volume : Measure (Fin N → Real)) {x | x i = 0} = 0 := by
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_eval_preimage_null (μ := fun _ : Fin N ↦ (volume : Measure Real))
      (i := i) (s := ({0} : Set Real)) (by simp)
  apply measure_mono_null (t := ⋃ i : Fin N, {x | x i = 0})
  · intro x hx
    have hx' : ¬ ∀ i, x i ≠ 0 := by
      simpa [allCoordinatesNonzero] using hx
    rw [mem_iUnion]
    by_contra hnone
    apply hx'
    intro i hi
    exact hnone ⟨i, hi⟩
  · exact measure_iUnion_null hhyperplane

/-- Coordinatewise inversion sends every polynomial zero set to a
Lebesgue-null set.  The possible nonsmooth points lie in the null union of
coordinate hyperplanes. -/
theorem volume_image_coordinatewiseInv_zeroSet_eq_zero {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    (volume : Measure (Fin N → Real))
        (coordinatewiseInv '' {x | MvPolynomial.eval x P = 0}) = 0 := by
  let Z : Set (Fin N → Real) := {x | MvPolynomial.eval x P = 0}
  let S : Set (Fin N → Real) := allCoordinatesNonzero
  have hZ : (volume : Measure (Fin N → Real)) Z = 0 :=
    volume_zeroSet_mvPolynomial_eval P hP
  have hgood : (volume : Measure (Fin N → Real))
      (coordinatewiseInv '' (Z ∩ S)) = 0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    · exact differentiableOn_coordinatewiseInv.mono inter_subset_right
    · exact measure_mono_null inter_subset_left hZ
  have hbadSubset : coordinatewiseInv '' (Z ∩ Sᶜ) ⊆ Sᶜ := by
    rintro x ⟨y, hyZ, rfl⟩
    have hybad : y ∈ Sᶜ := hyZ.2
    rw [mem_compl_iff] at hybad ⊢
    intro hinv
    apply hybad
    change ∀ i, y i ≠ 0
    intro i
    have hi := hinv i
    change (y i)⁻¹ ≠ 0 at hi
    simpa using hi
  have hbad : (volume : Measure (Fin N → Real))
      (coordinatewiseInv '' (Z ∩ Sᶜ)) = 0 :=
    measure_mono_null hbadSubset volume_compl_allCoordinatesNonzero_eq_zero
  change (volume : Measure (Fin N → Real)) (coordinatewiseInv '' Z) = 0
  rw [show Z = (Z ∩ S) ∪ (Z ∩ Sᶜ) by ext; simp, Set.image_union]
  exact measure_union_null hgood hbad

/-- Equivalently, a nonzero polynomial evaluated at inverse coordinates has
a Lebesgue-null zero event. -/
theorem volume_zeroSet_eval_coordinatewiseInv_eq_zero {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    (volume : Measure (Fin N → Real))
        {x | MvPolynomial.eval (coordinatewiseInv x) P = 0} = 0 := by
  have hset :
      {x : Fin N → Real | MvPolynomial.eval (coordinatewiseInv x) P = 0} =
        coordinatewiseInv '' {x | MvPolynomial.eval x P = 0} := by
    ext x
    constructor
    · intro hx
      refine ⟨coordinatewiseInv x, hx, ?_⟩
      exact coordinatewiseInv_involutive x
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hset]
  exact volume_image_coordinatewiseInv_zeroSet_eq_zero P hP

namespace RandomEnsemble

/-- The finite iid mass law also avoids a polynomial zero set after all
coordinates are inverted. -/
theorem finiteMassLaw_zeroSet_eval_coordinatewiseInv {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    finiteMassLaw N
        {x | MvPolynomial.eval (coordinatewiseInv x) P = 0} = 0 :=
  finiteMassLaw_absolutelyContinuous_volume N
    (volume_zeroSet_eval_coordinatewiseInv_eq_zero P hP)

end RandomEnsemble

namespace IIDMassPhaseEnsemble

variable {Omega : Type*} [MeasurableSpace Omega]

/-- In every verified iid ensemble, a nonzero polynomial of the inverse raw
mass coordinates vanishes with probability zero. -/
theorem probability_eval_inverse_restrictMassFin_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat}
    (P : MvPolynomial (Fin N) Real) (hP : P ≠ 0) :
    ensemble.probability
        {omega |
          MvPolynomial.eval
            (coordinatewiseInv (ensemble.restrictMassFin omega)) P = 0} = 0 := by
  have hLaw := ensemble.restrictMassFin_hasLaw (N := N)
  have hMeasurable : MeasurableSet
      {x : Fin N → Real |
        MvPolynomial.eval (coordinatewiseInv x) P = 0} := by
    apply MeasurableSet.preimage (isClosed_singleton.measurableSet)
    exact P.continuous_eval.measurable.comp
      (measurable_pi_lambda _ fun i ↦
        (measurable_pi_apply i).inv)
  exact (hLaw.measure_eq hMeasurable).trans
    (RandomEnsemble.finiteMassLaw_zeroSet_eval_coordinatewiseInv P hP)

end IIDMassPhaseEnsemble

end

end ArchonPhysics

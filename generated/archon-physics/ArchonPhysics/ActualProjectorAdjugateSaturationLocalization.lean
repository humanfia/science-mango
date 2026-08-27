import ArchonPhysics.ActualProjectorAdjugateSaturatedSpectralSystem
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Exact elimination of the Rabinowitsch variable

The saturated actual projector-minor system adjoins a variable `u` and the
relation `u * V - 1`, where `V` is the three-frequency Vandermonde.  This module
identifies that quotient ring exactly with localization of the genuine
mass/eigenvalue polynomial ring away from `V`.

This is a real elimination step, not a compatibility interface: under the
canonical `Option`-variable polynomial equivalence, the saturation equation is
the standard localization relation and each of the other four actual-model
equations is constant in `u`.  Thus the only variables still requiring
elimination are the three ordered eigenvalues; the repeated-eigenvalue
component has already been removed by making `V` invertible.
-/

namespace ArchonPhysics.ActualProjectorAdjugateSaturationLocalization

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualProjectorAdjugateSpectralSystem
open ArchonPhysics.ActualProjectorAdjugateSaturatedSpectralSystem

noncomputable section

abbrev AdjugateSpectralCoefficientRing (N : Nat) :=
  MvPolynomial (AdjugateSpectralVariable N) Real

/-- The standard univariate localization relation over the genuine
mass/eigenvalue coefficient ring. -/
def adjugateSpectralLocalizationRelation {N : Nat} :
    Polynomial (AdjugateSpectralCoefficientRing N) :=
  Polynomial.C (adjugateSpectralVandermonde (N := N)) * Polynomial.X - 1

/-- A polynomial independent of the new `Option.none` variable becomes a
constant polynomial under `optionEquivLeft`. -/
theorem optionEquivLeft_rename_some
    {N : Nat} (p : AdjugateSpectralCoefficientRing N) :
    MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
        (MvPolynomial.rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- The actual saturation equation is exactly the standard relation adjoining
the inverse of the Vandermonde. -/
theorem optionEquivLeft_adjugateSpectralSaturationEquation
    {N : Nat} :
    MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
        (adjugateSpectralSaturationEquation (N := N)) =
      adjugateSpectralLocalizationRelation (N := N) := by
  rw [adjugateSpectralSaturationEquation]
  rw [map_sub, map_mul, MvPolynomial.optionEquivLeft_X_none,
    optionEquivLeft_rename_some, MvPolynomial.optionEquivLeft_C]
  rw [Polynomial.X_mul_C]
  rfl

def adjugateSpectralSaturationIdeal {N : Nat} :
    Ideal (MvPolynomial (SaturatedAdjugateSpectralVariable N) Real) :=
  Ideal.span {adjugateSpectralSaturationEquation (N := N)}

def adjugateSpectralLocalizationRelationIdeal {N : Nat} :
    Ideal (Polynomial (AdjugateSpectralCoefficientRing N)) :=
  Ideal.span {adjugateSpectralLocalizationRelation (N := N)}

/-- The polynomial equivalence carries the actual saturation ideal onto the
standard localization-relation ideal. -/
theorem localizationRelationIdeal_eq_map_saturationIdeal
    {N : Nat} :
    adjugateSpectralLocalizationRelationIdeal (N := N) =
      (adjugateSpectralSaturationIdeal (N := N)).map
        (MvPolynomial.optionEquivLeft Real
          (AdjugateSpectralVariable N)).toRingEquiv.toRingHom := by
  unfold adjugateSpectralLocalizationRelationIdeal
  unfold adjugateSpectralSaturationIdeal
  rw [Ideal.map_span]
  simp only [Set.image_singleton]
  change Ideal.span {adjugateSpectralLocalizationRelation (N := N)} =
    Ideal.span
      {MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
        (adjugateSpectralSaturationEquation (N := N))}
  rw [optionEquivLeft_adjugateSpectralSaturationEquation]

/-- Quotienting by the actual Rabinowitsch equation is the standard adjoin-root
presentation with polynomial `V * X - 1`. -/
noncomputable def saturationQuotientEquivAdjoinRoot
    {N : Nat} :
    (MvPolynomial (SaturatedAdjugateSpectralVariable N) Real ⧸
        adjugateSpectralSaturationIdeal (N := N)) ≃ₐ[Real]
      AdjoinRoot (adjugateSpectralLocalizationRelation (N := N)) := by
  change
    (MvPolynomial (SaturatedAdjugateSpectralVariable N) Real ⧸
        adjugateSpectralSaturationIdeal (N := N)) ≃ₐ[Real]
      (Polynomial (AdjugateSpectralCoefficientRing N) ⧸
        adjugateSpectralLocalizationRelationIdeal (N := N))
  exact Ideal.quotientEquivAlg
    (adjugateSpectralSaturationIdeal (N := N))
    (adjugateSpectralLocalizationRelationIdeal (N := N))
    (MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N))
    localizationRelationIdeal_eq_map_saturationIdeal

/-- Exact elimination of `u`: the actual saturation quotient is localization
of the mass/eigenvalue polynomial ring away from the Vandermonde. -/
noncomputable def saturationQuotientEquivLocalization
    {N : Nat} :
    (MvPolynomial (SaturatedAdjugateSpectralVariable N) Real ⧸
        adjugateSpectralSaturationIdeal (N := N)) ≃ₐ[Real]
      Localization.Away (adjugateSpectralVandermonde (N := N)) :=
  (saturationQuotientEquivAdjoinRoot (N := N)).trans
    ((Localization.awayEquivAdjoin
      (adjugateSpectralVandermonde (N := N))).symm.restrictScalars Real)

/-- The defining Rabinowitsch polynomial is zero in its actual quotient. -/
theorem quotient_mk_adjugateSpectralSaturationEquation_eq_zero
    {N : Nat} :
    Ideal.Quotient.mk (adjugateSpectralSaturationIdeal (N := N))
        (adjugateSpectralSaturationEquation (N := N)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- Consequently the exact localization equivalence sends the actual
saturation equation to zero. -/
theorem saturationQuotientEquivLocalization_mk_saturationEquation_eq_zero
    {N : Nat} :
    saturationQuotientEquivLocalization (N := N)
        (Ideal.Quotient.mk (adjugateSpectralSaturationIdeal (N := N))
          (adjugateSpectralSaturationEquation (N := N))) = 0 := by
  rw [quotient_mk_adjugateSpectralSaturationEquation_eq_zero]
  exact map_zero _

/-- Each of the four actual adjugate/characteristic equations is independent
of `u` and becomes the corresponding constant coefficient polynomial. -/
theorem optionEquivLeft_renamed_actualThreeMassAdjugateSpectralSystem
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) (q : Fin 4) :
    MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
        (MvPolynomial.rename some
          (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q)) =
      Polynomial.C
        (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q) := by
  exact optionEquivLeft_rename_some _

/-- Complete exact `u`-elimination audit for the five actual equations: the
head is `V * X - 1`, and every successor is constant in `X`. -/
theorem optionEquivLeft_actualThreeMassSaturatedAdjugateSpectralSystem
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) :
    (MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
      (actualThreeMassSaturatedAdjugateSpectralSystem
        site₀ site₁ site₂ 0) =
      adjugateSpectralLocalizationRelation (N := N)) ∧
    (∀ q : Fin 4,
      MvPolynomial.optionEquivLeft Real (AdjugateSpectralVariable N)
        (actualThreeMassSaturatedAdjugateSpectralSystem
          site₀ site₁ site₂ (Fin.succ q)) =
        Polynomial.C
          (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q)) := by
  constructor
  · exact optionEquivLeft_adjugateSpectralSaturationEquation
  · intro q
    exact optionEquivLeft_renamed_actualThreeMassAdjugateSpectralSystem
      site₀ site₁ site₂ q

end

end ArchonPhysics.ActualProjectorAdjugateSaturationLocalization

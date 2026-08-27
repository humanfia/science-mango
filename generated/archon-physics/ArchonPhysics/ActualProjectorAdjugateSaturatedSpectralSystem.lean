import ArchonPhysics.ActualProjectorAdjugateSpectralSystem

/-!
# Vandermonde saturation of the actual projector-minor spectral system

The unsaturated adjugate/characteristic system has a diagonal spectral
component: assigning all three spectral variables to one eigenvalue solves it
for every mass configuration.  This module removes precisely that spurious
component by adjoining one Rabinowitsch variable `u` and the equation

`u * ((lambda_0 - lambda_1) * (lambda_0 - lambda_2) *
  (lambda_1 - lambda_2)) - 1 = 0`.

For an injective actual mode triple on simple spectrum, the reciprocal
Vandermonde gives a solution of the saturated system exactly when the genuine
actual projector-weight minor vanishes.  Conversely, every saturated solution
has pairwise distinct spectral coordinates.  This is the faithful input for a
later chamber-wise/resultant elimination; no nontriviality of that elimination
certificate is asserted here.
-/

namespace ArchonPhysics.ActualProjectorAdjugateSaturatedSpectralSystem

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualProjectorAdjugateSpectralSystem
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassResultantBridge
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- One extra variable is adjoined for the reciprocal Vandermonde. -/
abbrev SaturatedAdjugateSpectralVariable (N : Nat) :=
  Option (AdjugateSpectralVariable N)

/-- The three-variable Vandermonde factor that cuts out repeated spectral
parameters. -/
def adjugateSpectralVandermonde {N : Nat} :
    MvPolynomial (AdjugateSpectralVariable N) Real :=
  ((MvPolynomial.X
      (Sum.inr (0 : Fin 3) : AdjugateSpectralVariable N) -
    MvPolynomial.X
      (Sum.inr (1 : Fin 3) : AdjugateSpectralVariable N)) *
   (MvPolynomial.X
      (Sum.inr (0 : Fin 3) : AdjugateSpectralVariable N) -
    MvPolynomial.X
      (Sum.inr (2 : Fin 3) : AdjugateSpectralVariable N))) *
  (MvPolynomial.X
      (Sum.inr (1 : Fin 3) : AdjugateSpectralVariable N) -
    MvPolynomial.X
      (Sum.inr (2 : Fin 3) : AdjugateSpectralVariable N))

/-- Numerical Vandermonde value for three spectral parameters. -/
def spectralVandermondeValue (lambda : Fin 3 → Real) : Real :=
  ((lambda 0 - lambda 1) * (lambda 0 - lambda 2)) *
    (lambda 1 - lambda 2)

theorem evaluate_adjugateSpectralVandermonde
    {N : Nat} (x : Fin N → Real) (lambda : Fin 3 → Real) :
    MvPolynomial.eval (adjugateSpectralEvaluation x lambda)
        (adjugateSpectralVandermonde (N := N)) =
      spectralVandermondeValue lambda := by
  simp [adjugateSpectralVandermonde, spectralVandermondeValue,
    adjugateSpectralEvaluation]

theorem spectralVandermondeValue_ne_zero_of_injective
    (lambda : Fin 3 → Real) (hinjective : Function.Injective lambda) :
    spectralVandermondeValue lambda ≠ 0 := by
  unfold spectralVandermondeValue
  exact mul_ne_zero
    (mul_ne_zero
      (sub_ne_zero.mpr (hinjective.ne (by decide : (0 : Fin 3) ≠ 1)))
      (sub_ne_zero.mpr (hinjective.ne (by decide : (0 : Fin 3) ≠ 2))))
    (sub_ne_zero.mpr (hinjective.ne (by decide : (1 : Fin 3) ≠ 2)))

/-- Extend a mass/spectral evaluation by assigning the new variable the value
`u`. -/
def saturatedAdjugateSpectralEvaluation
    {N : Nat} (x : Fin N → Real) (lambda : Fin 3 → Real) (u : Real) :
    SaturatedAdjugateSpectralVariable N → Real
  | none => u
  | some v => adjugateSpectralEvaluation x lambda v

/-- Rabinowitsch equation making the Vandermonde invertible. -/
def adjugateSpectralSaturationEquation {N : Nat} :
    MvPolynomial (SaturatedAdjugateSpectralVariable N) Real :=
  MvPolynomial.X none *
      MvPolynomial.rename some (adjugateSpectralVandermonde (N := N)) -
    MvPolynomial.C 1

theorem evaluate_adjugateSpectralSaturationEquation
    {N : Nat} (g : SaturatedAdjugateSpectralVariable N → Real) :
    MvPolynomial.eval g (adjugateSpectralSaturationEquation (N := N)) =
      g none * MvPolynomial.eval (g ∘ some)
        (adjugateSpectralVandermonde (N := N)) - 1 := by
  simp [adjugateSpectralSaturationEquation, MvPolynomial.eval_rename]

theorem evaluate_adjugateSpectralSaturationEquation_at_values
    {N : Nat} (x : Fin N → Real) (lambda : Fin 3 → Real) (u : Real) :
    MvPolynomial.eval (saturatedAdjugateSpectralEvaluation x lambda u)
        (adjugateSpectralSaturationEquation (N := N)) =
      u * spectralVandermondeValue lambda - 1 := by
  rw [evaluate_adjugateSpectralSaturationEquation,
    ← evaluate_adjugateSpectralVandermonde x lambda]
  rfl

theorem evaluate_adjugateSpectralSaturationEquation_eq_zero_of_vandermonde_ne_zero
    {N : Nat} (x : Fin N → Real) (lambda : Fin 3 → Real)
    (hne : spectralVandermondeValue lambda ≠ 0) :
    MvPolynomial.eval
        (saturatedAdjugateSpectralEvaluation x lambda
          (spectralVandermondeValue lambda)⁻¹)
        (adjugateSpectralSaturationEquation (N := N)) = 0 := by
  rw [evaluate_adjugateSpectralSaturationEquation_at_values,
    inv_mul_cancel₀ hne]
  norm_num

theorem eval_vandermonde_ne_zero_of_saturationEquation_eq_zero
    {N : Nat} (g : SaturatedAdjugateSpectralVariable N → Real)
    (hzero : MvPolynomial.eval g
      (adjugateSpectralSaturationEquation (N := N)) = 0) :
    MvPolynomial.eval (g ∘ some)
        (adjugateSpectralVandermonde (N := N)) ≠ 0 := by
  intro hv
  rw [evaluate_adjugateSpectralSaturationEquation, hv] at hzero
  norm_num at hzero

/-- A saturated solution has pairwise distinct displayed spectral values. -/
theorem spectral_coordinates_ne_of_saturationEquation_eq_zero
    {N : Nat} (g : SaturatedAdjugateSpectralVariable N → Real)
    (hzero : MvPolynomial.eval g
      (adjugateSpectralSaturationEquation (N := N)) = 0) :
    g (some (Sum.inr (0 : Fin 3))) ≠
        g (some (Sum.inr (1 : Fin 3))) ∧
      g (some (Sum.inr (0 : Fin 3))) ≠
        g (some (Sum.inr (2 : Fin 3))) ∧
      g (some (Sum.inr (1 : Fin 3))) ≠
        g (some (Sum.inr (2 : Fin 3))) := by
  have hV := eval_vandermonde_ne_zero_of_saturationEquation_eq_zero g hzero
  have hprod :
      ((g (some (Sum.inr (0 : Fin 3))) -
          g (some (Sum.inr (1 : Fin 3)))) *
        (g (some (Sum.inr (0 : Fin 3))) -
          g (some (Sum.inr (2 : Fin 3))))) *
        (g (some (Sum.inr (1 : Fin 3))) -
          g (some (Sum.inr (2 : Fin 3)))) ≠ 0 := by
    simpa [adjugateSpectralVandermonde, Function.comp_def] using hV
  have h01 :
      g (some (Sum.inr (0 : Fin 3))) -
          g (some (Sum.inr (1 : Fin 3))) ≠ 0 := by
    intro h
    apply hprod
    simp [h]
  have h02 :
      g (some (Sum.inr (0 : Fin 3))) -
          g (some (Sum.inr (2 : Fin 3))) ≠ 0 := by
    intro h
    apply hprod
    simp [h]
  have h12 :
      g (some (Sum.inr (1 : Fin 3))) -
          g (some (Sum.inr (2 : Fin 3))) ≠ 0 := by
    intro h
    apply hprod
    simp [h]
  exact ⟨sub_ne_zero.mp h01, sub_ne_zero.mp h02, sub_ne_zero.mp h12⟩

/-- The actual three selected ordered eigenvalues. -/
def actualThreeMassSelectedEigenvalues
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : Fin 3 → Real :=
  fun r => orderedEigenvalue
    (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple) (modes r)

def actualThreeMassSpectralVandermonde
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : Real :=
  spectralVandermondeValue
    (actualThreeMassSelectedEigenvalues fixed site₀ site₁ site₂ modes triple)

theorem actualThreeMassSpectralVandermonde_ne_zero
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple))
    (hmodes : Function.Injective modes) :
    actualThreeMassSpectralVandermonde
      fixed site₀ site₁ site₂ modes triple ≠ 0 := by
  apply spectralVandermondeValue_ne_zero_of_injective
  unfold actualThreeMassSelectedEigenvalues
  exact hsimple.comp hmodes

/-- The actual mass/spectral point extended by the reciprocal Vandermonde. -/
def actualThreeMassSaturatedAdjugateSpectralPoint
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) : SaturatedAdjugateSpectralVariable N → Real :=
  saturatedAdjugateSpectralEvaluation
    (inverseMassCoordinates
      (threeMassSiteConfig fixed site₀ site₁ site₂ triple))
    (actualThreeMassSelectedEigenvalues fixed site₀ site₁ site₂ modes triple)
    (actualThreeMassSpectralVandermonde
      fixed site₀ site₁ site₂ modes triple)⁻¹

/-- Five equations: the saturation equation followed by the four genuine
adjugate/characteristic equations. -/
def actualThreeMassSaturatedAdjugateSpectralSystem
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) :
    Fin 5 → MvPolynomial (SaturatedAdjugateSpectralVariable N) Real :=
  Fin.cases
    (adjugateSpectralSaturationEquation (N := N))
    (fun q => MvPolynomial.rename some
      (actualThreeMassAdjugateSpectralSystem site₀ site₁ site₂ q))

theorem evaluate_renamed_actualThreeMassAdjugateSpectralPolynomial
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (p : MvPolynomial (AdjugateSpectralVariable N) Real) :
    MvPolynomial.eval
        (actualThreeMassSaturatedAdjugateSpectralPoint
          fixed site₀ site₁ site₂ modes triple)
        (MvPolynomial.rename some p) =
      MvPolynomial.eval
        (actualThreeMassAdjugateSpectralPoint
          fixed site₀ site₁ site₂ modes triple) p := by
  rw [MvPolynomial.eval_rename]
  congr 1

theorem evaluate_actualThreeMassSaturationEquation_eq_zero
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple))
    (hmodes : Function.Injective modes) :
    MvPolynomial.eval
        (actualThreeMassSaturatedAdjugateSpectralPoint
          fixed site₀ site₁ site₂ modes triple)
        (adjugateSpectralSaturationEquation (N := N)) = 0 := by
  unfold actualThreeMassSaturatedAdjugateSpectralPoint
  exact
    evaluate_adjugateSpectralSaturationEquation_eq_zero_of_vandermonde_ne_zero
      _ _ (actualThreeMassSpectralVandermonde_ne_zero
        fixed site₀ site₁ site₂ modes triple hsimple hmodes)

theorem actualThreeMassProjectorMinor_eq_zero_iff_saturatedSpectralSystem
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple))
    (hmodes : Function.Injective modes) :
    (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0 ↔
      ∀ q : Fin 5,
        MvPolynomial.eval
          (actualThreeMassSaturatedAdjugateSpectralPoint
            fixed site₀ site₁ site₂ modes triple)
          (actualThreeMassSaturatedAdjugateSpectralSystem
            site₀ site₁ site₂ q) = 0 := by
  constructor
  · intro hminor q
    refine Fin.cases ?_ (fun r => ?_) q
    · exact evaluate_actualThreeMassSaturationEquation_eq_zero
        fixed site₀ site₁ site₂ modes triple hsimple hmodes
    · simp [actualThreeMassSaturatedAdjugateSpectralSystem]
      rw [evaluate_renamed_actualThreeMassAdjugateSpectralPolynomial]
      exact
        (actualThreeMassProjectorMinor_eq_zero_iff_spectralSystem
          fixed site₀ site₁ site₂ modes triple hsimple).mp hminor r
  · intro hsystem
    apply
      (actualThreeMassProjectorMinor_eq_zero_iff_spectralSystem
        fixed site₀ site₁ site₂ modes triple hsimple).mpr
    intro r
    rw [← evaluate_renamed_actualThreeMassAdjugateSpectralPolynomial]
    simpa [actualThreeMassSaturatedAdjugateSpectralSystem] using
      hsystem (Fin.succ r)

end

end ArchonPhysics.ActualProjectorAdjugateSaturatedSpectralSystem

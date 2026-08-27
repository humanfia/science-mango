import ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
import ArchonPhysics.PolynomialMarkedLegWindowStrongLaw

/-!
# Complex polynomial marked-leg window strong law

Polynomial approximations to the cosine and sine components are combined into
three complex one-leg entries.  Their product is still a bounded continuous
fixed-window observable, so its spatial average converges almost surely along
every volume.
-/

namespace ArchonPhysics.ComplexPolynomialMarkedLegWindowStrongLaw

open ArchonPhysics
open ArchonPhysics.ComplexFiniteWindowIIDAllVolumeStrongLaw
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Product of three complex polynomial window legs, with independently
chosen zero-constant cosine and sine polynomials on each leg. -/
def complexThreeLegPolynomialWindowProduct {W : Nat} [NeZero W]
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W)
    (x : Fin W → Real) : Complex :=
  ∏ r : Fin 3, (
    (polynomialWindowKernelEntry
        (cosineDegree r) (cosineCoefficient r) (left r) (right r) x :
      Complex) +
      (polynomialWindowKernelEntry
        (sineDegree r) (sineCoefficient r) (left r) (right r) x :
      Complex) * Complex.I)

theorem continuous_complexThreeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    Continuous (complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient left right) := by
  unfold complexThreeLegPolynomialWindowProduct
  apply continuous_finsetProd
  intro r _hr
  exact
    (Complex.continuous_ofReal.comp
      (continuous_polynomialWindowKernelEntry
        (cosineDegree r) (cosineCoefficient r) (left r) (right r))).add
      ((Complex.continuous_ofReal.comp
        (continuous_polynomialWindowKernelEntry
          (sineDegree r) (sineCoefficient r) (left r) (right r))).mul
        continuous_const)

theorem measurable_complexThreeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    Measurable (complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient left right) :=
  (continuous_complexThreeLegPolynomialWindowProduct
    cosineDegree sineDegree cosineCoefficient sineCoefficient left right).measurable

theorem complexThreeLegPolynomialWindowProduct_clipWindow
    {W : Nat} [NeZero W]
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) (x : Fin W → Real) :
    complexThreeLegPolynomialWindowProduct
        cosineDegree sineDegree cosineCoefficient sineCoefficient left right
        (clipWindow x) =
      complexThreeLegPolynomialWindowProduct
        cosineDegree sineDegree cosineCoefficient sineCoefficient left right x := by
  unfold complexThreeLegPolynomialWindowProduct
  apply Finset.prod_congr rfl
  intro r _hr
  rw [polynomialWindowKernelEntry_clipWindow,
    polynomialWindowKernelEntry_clipWindow]

theorem exists_uniformBound_complexThreeLegPolynomialWindowProduct
    {W : Nat} [NeZero W]
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    ∃ C : Real, ∀ x : Fin W → Real,
      ‖complexThreeLegPolynomialWindowProduct
        cosineDegree sineDegree cosineCoefficient sineCoefficient
        left right x‖ ≤ C := by
  let K : Set (Fin W → Real) :=
    Set.pi Set.univ (fun _ ↦ massSupport)
  have hK : IsCompact K :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  let g : (Fin W → Real) → Real := fun x ↦
    ‖complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient
      left right x‖
  have hg : Continuous g :=
    (continuous_complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient
      left right).norm
  have hcompact : IsCompact (g '' K) := hK.image hg
  rcases hcompact.bddAbove with ⟨C, hC⟩
  refine ⟨C, fun x ↦ ?_⟩
  rw [← complexThreeLegPolynomialWindowProduct_clipWindow
    cosineDegree sineDegree cosineCoefficient sineCoefficient left right x]
  apply hC
  refine ⟨clipWindow x, ?_, rfl⟩
  intro i _hi
  exact clippedMass_mem_support (x i)

/-- All-volume almost-sure deterministic spatial limit for a product of three
complex polynomial marked legs. -/
theorem complexThreeLegPolynomialWindowProduct_allVolume_strongLaw_ae
    {W : Nat} [NeZero W]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (cosineDegree sineDegree : Fin 3 → Nat)
    (cosineCoefficient sineCoefficient : Fin 3 → Nat → Real)
    (left right : Fin 3 → Fin W) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦ complexSpatialAverage ensemble W
          (complexThreeLegPolynomialWindowProduct
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            left right) n omega)
        atTop
        (𝓝 (complexWindowMean ensemble W
          (complexThreeLegPolynomialWindowProduct
            cosineDegree sineDegree cosineCoefficient sineCoefficient
            left right))) := by
  obtain ⟨C, hC⟩ :=
    exists_uniformBound_complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient left right
  exact complexSpatialAverage_allVolume_strongLaw_ae
    ensemble W (NeZero.pos W)
    (complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient left right)
    (measurable_complexThreeLegPolynomialWindowProduct
      cosineDegree sineDegree cosineCoefficient sineCoefficient left right)
    C (fun x _hx ↦ hC x)

end


end ArchonPhysics.ComplexPolynomialMarkedLegWindowStrongLaw

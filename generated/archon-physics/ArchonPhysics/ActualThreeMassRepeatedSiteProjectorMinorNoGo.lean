import ArchonPhysics.ActualProjectorAdjugatePolynomial
import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
import ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail

/-!
# Repeated selected-site no-go for the actual projector minor

The three-mass chart is genuinely three dimensional only when its three
selected physical sites are distinct.  If two selected-site labels agree,
the corresponding cycle perturbation directions agree.  Hence the actual
projector-weight matrix has two equal columns for every mass realization and
every mode triple.

This obstruction already occurs in the joint inverse-mass/spectral-parameter
polynomial: its determinant is the zero polynomial.  Thus no resultant or
chamber elimination built from this numerator can manufacture a nonzero
witness in the repeated-site sector.  Equivalently, injectivity of the
selected-site map is a necessary structural condition for any nonzero minor
or nonzero adjugate numerator; it is not an optional genericity hypothesis.

The final theorem records the measure-level consequence without assuming
that the physical all-distinct collision source is positive: the complete
collision-weighted minor distribution is concentrated at zero.  Therefore a
zero-atom theorem in this sector can hold only when the whole physical source
measure vanishes.
-/

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassRepeatedSiteProjectorMinorNoGo

open ArchonPhysics
open ArchonPhysics.ActualProjectorAdjugatePolynomial
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorTail
open ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorZeroAtom
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- Equal selected physical sites give equal cycle perturbation directions. -/
theorem actualThreeMassCycleDirection_eq_of_selectedSite_eq
    {N : Nat} [NeZero N]
    (site₀ site₁ site₂ : Lattice.Site N) (s t : Fin 3)
    (hsite : actualThreeMassSelectedSite site₀ site₁ site₂ s =
      actualThreeMassSelectedSite site₀ site₁ site₂ t) :
    actualThreeMassCycleDirection site₀ site₁ site₂ s =
      actualThreeMassCycleDirection site₀ site₁ site₂ t := by
  simp only [actualThreeMassCycleDirection]
  rw [hsite]

/-- A repeated selected site forces the genuine projector minor to vanish
pointwise, independently of spectrum simplicity and of the mode labels. -/
theorem actualThreeMassProjectorWeightMatrix_det_eq_zero_of_selectedSite_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple) (s t : Fin 3) (hst : s ≠ t)
    (hsite : actualThreeMassSelectedSite site₀ site₁ site₂ s =
      actualThreeMassSelectedSite site₀ site₁ site₂ t) :
    (actualThreeMassProjectorWeightMatrix
      fixed site₀ site₁ site₂ modes triple).det = 0 := by
  apply Matrix.det_zero_of_column_eq hst
  intro r
  unfold actualThreeMassProjectorWeightMatrix
    orderedProjectorWeightMatrix
  rw [actualThreeMassCycleDirection_eq_of_selectedSite_eq
    site₀ site₁ site₂ s t hsite]

/-- The exact joint adjugate numerator is already the zero polynomial in the
repeated-site sector, before any spectral variable is eliminated. -/
theorem actualThreeMassAdjugateSpectralPolynomial_eq_zero_of_selectedSite_eq
    {N : Nat} [NeZero N] (site₀ site₁ site₂ : Lattice.Site N)
    (s t : Fin 3) (hst : s ≠ t)
    (hsite : actualThreeMassSelectedSite site₀ site₁ site₂ s =
      actualThreeMassSelectedSite site₀ site₁ site₂ t) :
    actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂ = 0 := by
  unfold actualThreeMassAdjugateSpectralPolynomial
    symbolicAdjugateWeightDetPolynomial
  apply Matrix.det_zero_of_column_eq hst
  intro r
  unfold symbolicAdjugateWeightMatrix
  rw [actualThreeMassCycleDirection_eq_of_selectedSite_eq
    site₀ site₁ site₂ s t hsite]

/-- A nonzero genuine projector minor can occur only in the injective
selected-site sector. -/
theorem selectedSites_injective_of_projectorWeightMatrix_det_ne_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : MassTriple)
    (hminor : (actualThreeMassProjectorWeightMatrix
      fixed site₀ site₁ site₂ modes triple).det ≠ 0) :
    Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂) := by
  intro s t hsite
  by_contra hst
  exact hminor
    (actualThreeMassProjectorWeightMatrix_det_eq_zero_of_selectedSite_eq
      fixed site₀ site₁ site₂ modes triple s t hst hsite)

/-- Likewise, nontriviality of the explicit adjugate numerator forces the
three selected physical sites to be distinct. -/
theorem selectedSites_injective_of_adjugateSpectralPolynomial_ne_zero
    {N : Nat} [NeZero N] (site₀ site₁ site₂ : Lattice.Site N)
    (hnumerator :
      actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂ ≠ 0) :
    Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂) := by
  intro s t hsite
  by_contra hst
  exact hnumerator
    (actualThreeMassAdjugateSpectralPolynomial_eq_zero_of_selectedSite_eq
      site₀ site₁ site₂ s t hst hsite)

/-- Noninjectivity therefore implies an unconditional collapse of
the explicit joint adjugate numerator to the zero polynomial. -/
theorem actualThreeMassAdjugateSpectralPolynomial_eq_zero_of_not_injective
    {N : Nat} [NeZero N] (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂)) :
    actualThreeMassAdjugateSpectralPolynomial site₀ site₁ site₂ = 0 := by
  by_contra hnumerator
  exact hsite
    (selectedSites_injective_of_adjugateSpectralPolynomial_ne_zero
      site₀ site₁ site₂ hnumerator)


/-- With a noninjective selected-site map, every actual projector-minor
magnitude is identically zero. -/
theorem actualThreeMassProjectorMinorMagnitude_eq_zero_of_not_injective
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂))
    (modes : OrderedModeTriple N) (triple : MassTriple) :
    actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes triple = 0 := by
  rw [actualThreeMassProjectorMinorMagnitude, abs_eq_zero]
  by_contra hminor
  exact hsite
    (selectedSites_injective_of_projectorWeightMatrix_det_ne_zero
      fixed site₀ site₁ site₂ modes triple hminor)

/-- Thus every modewise zero locus is the whole raw mass space. -/
theorem actualThreeMassProjectorMinorZeroSet_eq_univ_of_not_injective
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂))
    (modes : OrderedModeTriple N) :
    actualThreeMassProjectorMinorZeroSet
      fixed site₀ site₁ site₂ modes = univ := by
  ext triple
  simp [actualThreeMassProjectorMinorZeroSet,
    actualThreeMassProjectorMinorMagnitude_eq_zero_of_not_injective
      fixed site₀ site₁ site₂ hsite modes triple]

/-- Strong measure-level no-go: in the repeated-site sector, the complete
physical all-distinct collision-weighted projector-minor law is concentrated
at zero.  In particular its zero atom equals its entire mass. -/
theorem actualThreeMassCollisionWeightedProjectorMinorDistribution_singleton_zero_eq_univ_of_not_injective
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (hsite : ¬ Function.Injective
      (actualThreeMassSelectedSite site₀ site₁ site₂)) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ ({0} : Set Real) =
      actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
        fixed site₀ site₁ site₂ univ := by
  rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_singleton_zero_eq,
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution_univ_eq]
  apply congrArg (fun x : ENNReal => (N : ENNReal)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [actualThreeMassProjectorMinorZeroSet_eq_univ_of_not_injective
    fixed site₀ site₁ site₂ hsite modes]

end

end ArchonPhysics.ActualThreeMassRepeatedSiteProjectorMinorNoGo

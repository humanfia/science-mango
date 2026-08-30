import ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber
import ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
import ArchonPhysics.TwoParameterSpectralPolynomialAvoidance

/-!
# Almost-everywhere four-site opposite canonical resultant

For the four-cycle pair fiber varying sites `0,2`, the frozen complement is
exactly sites `1,3`.  Reindex its finite iid law as the standard two-mass
product law.  Continuity of the one-site mass law makes the diagonal null,
so the two frozen inverse weights differ almost everywhere.  The exact
factorization from `FourSiteOppositeCanonicalResultantFrozenFiber` then gives
the canonical resultant nonvanishing assumption required by the generic
single-frequency closure.
-/

namespace ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiber
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set

noncomputable section

/-- The two frozen indices left after varying sites `0` and `2`. -/
abbrev oppositeFrozenComplement : Finset Nat :=
  finiteVolumeMassPairComplement
    (0 : Lattice.Site 4) (2 : Lattice.Site 4)

/-- Site `1` as an element of the frozen complement. -/
def frozenSiteOneIndex : oppositeFrozenComplement :=
  ⟨1, by
    norm_num +decide [oppositeFrozenComplement,
      finiteVolumeMassPairComplement, selectedMassPairIndices]⟩

/-- Site `3` as an element of the frozen complement. -/
def frozenSiteThreeIndex : oppositeFrozenComplement :=
  ⟨3, by
    norm_num +decide [oppositeFrozenComplement,
      finiteVolumeMassPairComplement, selectedMassPairIndices]⟩

/-- The frozen complement is canonically ordered as sites `1,3`. -/
def oppositeFrozenIndexEquiv : Fin 2 ≃ oppositeFrozenComplement where
  toFun i := if i = 0 then frozenSiteOneIndex else frozenSiteThreeIndex
  invFun i := if i.1 = 1 then 0 else 1
  left_inv i := by
    fin_cases i <;>
      simp [frozenSiteOneIndex, frozenSiteThreeIndex]
  right_inv i := by
    apply Subtype.ext
    have hmem := i.property
    have hlt : i.1 < 4 := by
      exact Finset.mem_range.mp (Finset.mem_sdiff.mp hmem).1
    have hne0 : i.1 ≠ 0 := by
      intro hi
      have hnot := (Finset.mem_sdiff.mp hmem).2
      apply hnot
      norm_num +decide [selectedMassPairIndices, hi] at hnot
    have hne2 : i.1 ≠ 2 := by
      intro hi
      have hnot := (Finset.mem_sdiff.mp hmem).2
      apply hnot
      rw [hi, show (2 : Lattice.Site 4).val = 2 by decide]
      simp [selectedMassPairIndices]
    have hor : i.1 = 1 ∨ i.1 = 3 := by omega
    rcases hor with hi | hi
    · simp [hi, frozenSiteOneIndex]
    · simp [hi, frozenSiteThreeIndex]

@[simp] theorem oppositeFrozenIndexEquiv_zero :
    oppositeFrozenIndexEquiv 0 = frozenSiteOneIndex := rfl

@[simp] theorem oppositeFrozenIndexEquiv_one :
    oppositeFrozenIndexEquiv 1 = frozenSiteThreeIndex := by
  simp [oppositeFrozenIndexEquiv]

/-- Read the two frozen masses in physical site order `1,3`. -/
def oppositeFrozenMassPair
    (rest : FiniteMassVector oppositeFrozenComplement) : Real × Real :=
  (rest frozenSiteOneIndex, rest frozenSiteThreeIndex)

theorem measurable_oppositeFrozenMassPair :
    Measurable oppositeFrozenMassPair := by
  exact (measurable_pi_apply frozenSiteOneIndex).prodMk
    (measurable_pi_apply frozenSiteThreeIndex)

/-- Reindexing the exact four-site frozen complement produces precisely the
standard iid two-mass product law. -/
theorem measurePreserving_oppositeFrozenMassPair :
    MeasurePreserving oppositeFrozenMassPair
      (iidFiniteMassVectorLaw oppositeFrozenComplement)
      iidMassPairLaw := by
  let e :
      (FiniteMassVector oppositeFrozenComplement) ≃ᵐ (Fin 2 → Real) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : oppositeFrozenComplement => Real)
      oppositeFrozenIndexEquiv).symm
  have hreindex : MeasurePreserving e
      (iidFiniteMassVectorLaw oppositeFrozenComplement)
      (Measure.pi fun _ : Fin 2 => massCoordinateLaw) := by
    exact MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : oppositeFrozenComplement => Real)
        oppositeFrozenIndexEquiv)
      (measurePreserving_piCongrLeft
        (fun _ : oppositeFrozenComplement => massCoordinateLaw)
        oppositeFrozenIndexEquiv)
  have hpair :=
    (measurePreserving_finTwoArrow massCoordinateLaw).comp hreindex
  have hfun : oppositeFrozenMassPair =
      MeasurableEquiv.finTwoArrow ∘ e := by
    funext rest
    apply Prod.ext <;> rfl
  rw [hfun]
  exact hpair

/-- The diagonal equation for the two inverse frozen masses. -/
def frozenInverseDiagonalPolynomial : MvPolynomial (Fin 2) Real :=
  MvPolynomial.X 0 - MvPolynomial.X 1

@[simp] theorem frozenInverseDiagonalPolynomial_eval
    (pair : Real × Real) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
        frozenInverseDiagonalPolynomial = pair.1⁻¹ - pair.2⁻¹ := by
  simp [frozenInverseDiagonalPolynomial]

theorem frozenInverseDiagonalPolynomial_ne_zero :
    frozenInverseDiagonalPolynomial ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (![1, (2 : Real)] : Fin 2 → Real)) hzero
  norm_num [frozenInverseDiagonalPolynomial] at heval

/-- Two independent continuously distributed raw masses have distinct
inverse masses almost everywhere. -/
theorem iidMassPair_inverse_ne_ae :
    ∀ᵐ pair ∂iidMassPairLaw, pair.1⁻¹ ≠ pair.2⁻¹ := by
  have hzero := iidMassPairLaw_zeroSet_eval_inverseCoordinates
    frozenInverseDiagonalPolynomial
    frozenInverseDiagonalPolynomial_ne_zero
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero]
    with pair hpair
  simpa only [mem_setOf_eq, frozenInverseDiagonalPolynomial_eval,
    sub_eq_zero, not_false_eq_true] using hpair

/-- The iid mass pair belongs to its closed support square almost
everywhere. -/
theorem iidMassPair_mem_support_ae :
    ∀ᵐ pair ∂iidMassPairLaw, pair ∈ iidMassPairSupport := by
  rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
    filter_upwards [massCoordinate_mem_support_ae] with second hsecond
    exact ⟨hfirst, hsecond⟩
  · exact measurableSet_Icc.prod measurableSet_Icc

/-- Clipping is invisible under the physical iid law, hence the two positive
frozen inverse masses remain distinct almost everywhere. -/
theorem iidMassPair_clipped_inverse_ne_ae :
    ∀ᵐ pair ∂iidMassPairLaw,
      (clippedMass pair.1)⁻¹ ≠ (clippedMass pair.2)⁻¹ := by
  filter_upwards [iidMassPair_mem_support_ae, iidMassPair_inverse_ne_ae]
    with pair hsupport hne
  simpa [clippedMass_eq_self hsupport.1,
    clippedMass_eq_self hsupport.2] using hne

/-- The site-`1` frozen inverse weight is the clipped inverse of the first
frozen-complement coordinate. -/
@[simp] theorem frozenInverseWeightOne_finitePairEnvironment
    (rest : FiniteMassVector oppositeFrozenComplement) :
    frozenInverseWeightOne
        (finitePairEnvironmentPositiveMassConfig
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) =
      (clippedMass (rest frozenSiteOneIndex))⁻¹ := by
  change
    (if hmem : (1 : Lattice.Site 4).val ∈
        finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) then
      clippedMass (rest ⟨(1 : Lattice.Site 4).val, hmem⟩)
    else massLower)⁻¹ =
      (clippedMass (rest frozenSiteOneIndex))⁻¹
  rw [show (1 : Lattice.Site 4).val = 1 by decide]
  have hmem : 1 ∈ finiteVolumeMassPairComplement
      (0 : Lattice.Site 4) (2 : Lattice.Site 4) :=
    frozenSiteOneIndex.property
  rw [dif_pos hmem]
  have hindex :
      (⟨1, hmem⟩ : oppositeFrozenComplement) = frozenSiteOneIndex := by
    apply Subtype.ext
    rfl
  rw [hindex]

/-- The site-`3` frozen inverse weight is the clipped inverse of the second
frozen-complement coordinate. -/
@[simp] theorem frozenInverseWeightThree_finitePairEnvironment
    (rest : FiniteMassVector oppositeFrozenComplement) :
    frozenInverseWeightThree
        (finitePairEnvironmentPositiveMassConfig
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) =
      (clippedMass (rest frozenSiteThreeIndex))⁻¹ := by
  change
    (if hmem : (3 : Lattice.Site 4).val ∈
        finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) then
      clippedMass (rest ⟨(3 : Lattice.Site 4).val, hmem⟩)
    else massLower)⁻¹ =
      (clippedMass (rest frozenSiteThreeIndex))⁻¹
  rw [show (3 : Lattice.Site 4).val = 3 by decide]
  have hmem : 3 ∈ finiteVolumeMassPairComplement
      (0 : Lattice.Site 4) (2 : Lattice.Site 4) :=
    frozenSiteThreeIndex.property
  rw [dif_pos hmem]
  have hindex :
      (⟨3, hmem⟩ : oppositeFrozenComplement) = frozenSiteThreeIndex := by
    apply Subtype.ext
    rfl
  rw [hindex]

/-- Under the exact iid frozen-complement law, the two frozen inverse
weights differ almost everywhere. -/
theorem frozenInverseWeights_ne_ae :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw oppositeFrozenComplement),
      frozenInverseWeightOne
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) ≠
        frozenInverseWeightThree
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) := by
  have hpullback : ∀ᵐ rest ∂
      (iidFiniteMassVectorLaw oppositeFrozenComplement),
      (clippedMass (oppositeFrozenMassPair rest).1)⁻¹ ≠
        (clippedMass (oppositeFrozenMassPair rest).2)⁻¹ := by
    exact measurePreserving_oppositeFrozenMassPair.quasiMeasurePreserving.ae iidMassPair_clipped_inverse_ne_ae
  filter_upwards [hpullback] with rest hrest
  simpa [oppositeFrozenMassPair] using hrest

/-- Exact frozen-rest hypothesis required by the generic canonical-resultant
closure: on the four-cycle opposite pair fiber, it holds automatically under
the continuous iid frozen-complement law. -/
theorem twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw oppositeFrozenComplement),
      twoSitePositiveCharacteristicJacobianResultant
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) ≠ 0 := by
  filter_upwards [frozenInverseWeights_ne_ae] with rest hfrozen
  exact twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero _
    hfrozen

end


end ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere

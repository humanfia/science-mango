import ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness

/-!
# Evenness obstruction for the six-site near-resonant path

The symmetric raw-mass path swaps its first two masses under `t ↦ -t`.
Its exact characteristic polynomial depends only on `t²`, hence every
ordered frequency and the selected decay mismatch are even functions of the
path parameter.  In particular, the two sides of the clean resonant point
cannot furnish an IVT sign-changing certificate.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantMismatchEven

open ArchonPhysics
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteNearResonantPathSimpleSpectrum
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Polynomial Set

noncomputable section

/-- The symmetric iid support is preserved by negating the scalar path
parameter, which swaps the first two raw masses. -/
theorem nearResonantMassTriple_neg_mem_support
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport) :
    nearResonantMassTriple (-t) ∈ iidMassTripleSupport := by
  change ((1 - t ∈ massSupport ∧ 1 + t ∈ massSupport) ∧
    (1 : Real) ∈ massSupport) at hsupport
  change ((1 - (-t) ∈ massSupport ∧ 1 + (-t) ∈ massSupport) ∧
    (1 : Real) ∈ massSupport)
  rcases hsupport with ⟨⟨hzero, hone⟩, htwo⟩
  exact ⟨⟨by convert hone using 1; ring,
      by convert hzero using 1; ring⟩, htwo⟩
/-- The genuine physical characteristic polynomial is even along the
symmetric reciprocal-mass path. -/
theorem actualSixSiteNearResonant_charpoly_neg_eq
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) :
    Matrix.charpoly
        (Matrix.of (actualSixSiteThreeMassHarmonic
          (nearResonantMassTriple (-t))).val) =
      Matrix.charpoly
        (Matrix.of (actualSixSiteThreeMassHarmonic
          (nearResonantMassTriple t)).val) := by
  have hsupportNeg := nearResonantMassTriple_neg_mem_support hsupport
  have hpoleNeg : 1 - (-t) ^ 2 ≠ 0 := by
    simpa only [neg_sq] using hpole
  apply Polynomial.funext
  intro energy
  rw [actualSixSiteNearResonant_charpoly_eval hsupportNeg hpoleNeg,
    actualSixSiteNearResonant_charpoly_eval hsupport hpole]
  ring

/-- Equal characteristic polynomials give equality of every decreasingly
ordered squared frequency. -/
theorem actualSixSiteNearResonant_orderedEigenvalue_neg_eq
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0)
    (k : Fin (Fintype.card (Lattice.Site 6))) :
    orderedEigenvalue
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple (-t))) k =
      orderedEigenvalue
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) k := by
  let A := actualSixSiteThreeMassHarmonic (nearResonantMassTriple (-t))
  let B := actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)
  have hchar : Matrix.charpoly (Matrix.of A.val) =
      Matrix.charpoly (Matrix.of B.val) := by
    simpa [A, B] using actualSixSiteNearResonant_charpoly_neg_eq hsupport hpole
  have heigenvalues : A.property.eigenvalues = B.property.eigenvalues :=
    (A.property.eigenvalues_eq_eigenvalues_iff B.property).2 hchar
  let e : Fin (Fintype.card (Lattice.Site 6)) ≃ Lattice.Site 6 :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hselected := congrFun heigenvalues (e k)
  simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, e] using hselected

/-- Every selected physical ordered frequency is even on the path. -/
theorem actualSixSiteNearResonant_orderedModeFrequency_neg_eq
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0)
    (k : Fin (Fintype.card (Lattice.Site 6))) :
    orderedModeFrequency
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple (-t))) k =
      orderedModeFrequency
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) k := by
  unfold orderedModeFrequency
  rw [actualSixSiteNearResonant_orderedEigenvalue_neg_eq hsupport hpole]

/-- The selected `(+,-,-)` six-site mismatch is even.  Thus the points `t`
and `-t` can never be the opposite-sign endpoints of an IVT crossing. -/
theorem actualSixSiteNearResonantMismatchPath_neg_eq
    {t : Real} (hsupport : nearResonantMassTriple t ∈ iidMassTripleSupport)
    (hpole : 1 - t ^ 2 ≠ 0) :
    actualSixSiteNearResonantMismatchPath (-t) =
      actualSixSiteNearResonantMismatchPath t := by
  change
    (∑ r : Fin 3,
      (ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign r).coefficient *
        orderedModeFrequency
          (actualSixSiteThreeMassHarmonic (nearResonantMassTriple (-t)))
          (ActualSixSiteCleanDecayResonancePatch.cleanSixSiteDecayModes r)) =
      ∑ r : Fin 3,
        (ActualThreeMassLiftedJacobianPolynomial.actualFourSiteDecaySign r).coefficient *
          orderedModeFrequency
            (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t))
            (ActualSixSiteCleanDecayResonancePatch.cleanSixSiteDecayModes r)
  apply Finset.sum_congr rfl
  intro r _hr
  simp_rw [actualSixSiteNearResonant_orderedModeFrequency_neg_eq
    hsupport hpole]

end

end ArchonPhysics.ActualSixSiteNearResonantMismatchEven

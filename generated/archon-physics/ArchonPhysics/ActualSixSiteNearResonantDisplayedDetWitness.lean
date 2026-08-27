import ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness

/-!
# Nonzero displayed adjugate determinant on the six-site path

This module combines simple spectrum, positivity of the selected physical
energies, and the exact alternant factorization to turn the nonzero residual
path witness into a nonzero three-by-three displayed adjugate determinant.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantDisplayedDetWitness

open ArchonPhysics
open ArchonPhysics.ActualSixSiteCleanDecayResonancePatch
open ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
open ArchonPhysics.ActualSixSiteNearResonantJacobianWitness
open ArchonPhysics.ActualSixSiteNearResonantPathResidualWitness
open ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- At a simple nonzero path point with nonzero symmetric residual, the exact
displayed adjugate-weight determinant cannot vanish. -/
theorem nearResonantAdjugateWeightMatrix_det_ne_zero_of_path
    {t : Real} (ht : t ≠ 0)
    (hsimple : SimpleOrderedSpectrum
      (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)))
    (hresidual : actualSixSiteNearResonantAdjugateResidualPath t ≠ 0)
    (hpole : 1 - t ^ 2 ≠ 0) :
    (nearResonantAdjugateWeightMatrix t
      (actualSixSiteNearResonantSelectedEnergy t)).det ≠ 0 := by
  have hprod : (1 - t) * (1 + t) ≠ 0 := by
    rw [show (1 - t) * (1 + t) = 1 - t ^ 2 by ring]
    exact hpole
  have hleft : 1 - t ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hright : 1 + t ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hminus : t - 1 ≠ 0 := by
    intro h
    apply hleft
    linarith
  have hplus : t + 1 ≠ 0 := by
    intro h
    apply hright
    linarith
  have hpositive : ∀ r, 0 < actualSixSiteNearResonantSelectedEnergy t r := by
    intro r
    simpa [actualSixSiteNearResonantSelectedEnergy] using
      actualSixSiteDecayModes_energy_pos_of_simple
        (nearResonantMassTriple t) hsimple r
  have hzeroOne :
      actualSixSiteNearResonantSelectedEnergy t 0 ≠
        actualSixSiteNearResonantSelectedEnergy t 1 := by
    intro h
    have hmodes := hsimple h
    exact (by decide :
      cleanSixSiteDecayModes (0 : Fin 3) ≠
        cleanSixSiteDecayModes (1 : Fin 3)) hmodes
  have hzeroTwo :
      actualSixSiteNearResonantSelectedEnergy t 0 ≠
        actualSixSiteNearResonantSelectedEnergy t 2 := by
    intro h
    have hmodes := hsimple h
    exact (by decide :
      cleanSixSiteDecayModes (0 : Fin 3) ≠
        cleanSixSiteDecayModes (2 : Fin 3)) hmodes
  have honeTwo :
      actualSixSiteNearResonantSelectedEnergy t 1 ≠
        actualSixSiteNearResonantSelectedEnergy t 2 := by
    intro h
    have hmodes := hsimple h
    exact (by decide :
      cleanSixSiteDecayModes (1 : Fin 3) ≠
        cleanSixSiteDecayModes (2 : Fin 3)) hmodes
  have hresidual' :
      nearResonantAdjugateResidual t
        (actualSixSiteNearResonantSelectedEnergy t) ≠ 0 := by
    simpa [actualSixSiteNearResonantAdjugateResidualPath] using hresidual
  have hnum :
      4 * actualSixSiteNearResonantSelectedEnergy t 0 *
          actualSixSiteNearResonantSelectedEnergy t 1 *
          actualSixSiteNearResonantSelectedEnergy t 2 * t ^ 2 *
          (actualSixSiteNearResonantSelectedEnergy t 0 -
            actualSixSiteNearResonantSelectedEnergy t 1) *
          (actualSixSiteNearResonantSelectedEnergy t 0 -
            actualSixSiteNearResonantSelectedEnergy t 2) *
          (actualSixSiteNearResonantSelectedEnergy t 1 -
            actualSixSiteNearResonantSelectedEnergy t 2) *
          nearResonantAdjugateResidual t
            (actualSixSiteNearResonantSelectedEnergy t) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (mul_ne_zero
                  (mul_ne_zero (by norm_num) (ne_of_gt (hpositive 0)))
                  (ne_of_gt (hpositive 1)))
                (ne_of_gt (hpositive 2)))
              (pow_ne_zero 2 ht))
            (sub_ne_zero.mpr hzeroOne))
          (sub_ne_zero.mpr hzeroTwo))
        (sub_ne_zero.mpr honeTwo))
      hresidual'
  have hden : (t - 1) ^ 2 * (t + 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hminus) (pow_ne_zero 2 hplus)
  rw [nearResonantAdjugateWeightMatrix_det _ _ hminus hplus]
  exact div_ne_zero hnum hden

/-- Every positive mismatch width contains an explicit positive path point
whose displayed adjugate determinant is nonzero. -/
theorem exists_actualSixSiteNearResonantDisplayedDetWitness
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Real,
      0 < t ∧
      nearResonantMassTriple t ∈ interior iidMassTripleSupport ∧
      |actualSixSiteNearResonantMismatchPath t| < epsilon ∧
      SimpleOrderedSpectrum
        (actualSixSiteThreeMassHarmonic (nearResonantMassTriple t)) ∧
      (nearResonantAdjugateWeightMatrix t
        (actualSixSiteNearResonantSelectedEnergy t)).det ≠ 0 ∧
      1 - t ^ 2 ≠ 0 := by
  obtain ⟨t, ht, hinterior, hmismatch, hsimple, hresidual, hpole⟩ :=
    exists_actualSixSiteNearResonantPathResidualWitness hepsilon
  exact ⟨t, ht, hinterior, hmismatch, hsimple,
    nearResonantAdjugateWeightMatrix_det_ne_zero_of_path
      (ne_of_gt ht) hsimple hresidual hpole,
    hpole⟩

end

end ArchonPhysics.ActualSixSiteNearResonantDisplayedDetWitness

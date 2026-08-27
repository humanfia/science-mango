import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

/-!
# Consumer: second-order Haar algebra for finite character families

This consumer instantiates the family-level phase expansion on a five-site
phase torus with independently indexed zeroth, first, and second supplied
coefficients.  The second-order endpoint displays both complete ordered-pair
sums, so distinct terms with equal charge remain visible.

The result is finite phase algebra.  It does not construct the supplied
coefficients from a microscopic flow or call either summand a collision
operator or an FGR coefficient.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderCharacterFamilyExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The complete five-site second-order coefficient: all equal-charge
`A1`/`A1` ordered pairs plus all equal-charge `A0`/`A2` interference pairs. -/
theorem fiveSite_finiteCharacterFamily_secondOrder_contract
    (zCoefficient : Fin 2 → Complex)
    (zCharge : Fin 2 → Lattice.Site 5 → Int)
    (wCoefficient : Fin 4 → Complex)
    (wCharge : Fin 4 → Lattice.Site 5 → Int)
    (uCoefficient : Fin 6 → Complex)
    (uCharge : Fin 6 → Lattice.Site 5 → Int) :
    (∫ phase : UnitAddTorus (Lattice.Site 5),
      twoStepSecondCoefficient
        (finitePhaseCorrection zCoefficient zCharge phase)
        (finitePhaseCorrection wCoefficient wCharge phase)
        (finitePhaseCorrection uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw (Lattice.Site 5)) =
      (∑ left : Fin 4, ∑ right : Fin 4,
        if wCharge left = wCharge right then
          wCoefficient left * starRingEnd Complex (wCoefficient right)
        else 0).re +
      2 * (∑ left : Fin 2, ∑ right : Fin 6,
        if zCharge left = uCharge right then
          zCoefficient left * starRingEnd Complex (uCoefficient right)
        else 0).re := by
  simpa [finiteCharacterFamilySecondOrderCoefficient,
    sameChargeFamilySquare, equalChargeFamilyInterference,
    equalChargeCrossPairSum] using
      (integral_twoStepSecondCoefficient_finitePhaseCorrections
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge)

/-- First-order interference is selected by equality of the complete charge
vectors of the two finite families. -/
theorem fiveSite_finiteCharacterFamily_firstOrder_contract
    (zCoefficient : Fin 2 → Complex)
    (zCharge : Fin 2 → Lattice.Site 5 → Int)
    (wCoefficient : Fin 4 → Complex)
    (wCharge : Fin 4 → Lattice.Site 5 → Int) :
    (∫ phase : UnitAddTorus (Lattice.Site 5),
      secondMomentFirst
        (finitePhaseCorrection zCoefficient zCharge phase)
        (finitePhaseCorrection wCoefficient wCharge phase)
      ∂finitePhaseHaarLaw (Lattice.Site 5)) =
      2 * (∑ left : Fin 2, ∑ right : Fin 4,
        if zCharge left = wCharge right then
          zCoefficient left * starRingEnd Complex (wCoefficient right)
        else 0).re := by
  simpa [equalChargeFamilyInterference, equalChargeCrossPairSum] using
    (integral_twoStepFirstCoefficient_finitePhaseCorrections
      zCoefficient zCharge wCoefficient wCharge)

/-- The whole supplied two-step amplitude has the exact family-level Haar
moment polynomial, with the preceding second-order coefficient in its
`epsilon^2` slot. -/
theorem fiveSite_finiteCharacterFamily_fullMoment_contract
    (epsilon : Real)
    (zCoefficient : Fin 2 → Complex)
    (zCharge : Fin 2 → Lattice.Site 5 → Int)
    (wCoefficient : Fin 4 → Complex)
    (wCharge : Fin 4 → Lattice.Site 5 → Int)
    (uCoefficient : Fin 6 → Complex)
    (uCharge : Fin 6 → Lattice.Site 5 → Int) :
    (∫ phase : UnitAddTorus (Lattice.Site 5),
      Complex.normSq
        (finiteCharacterFamilyTwoStepAmplitude epsilon
          zCoefficient zCharge wCoefficient wCharge
          uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw (Lattice.Site 5)) =
      finiteCharacterFamilyTwoStepMomentPolynomial epsilon
        zCoefficient zCharge wCoefficient wCharge
        uCoefficient uCharge := by
  exact integral_normSq_finiteCharacterFamilyTwoStepAmplitude epsilon
    zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge

#print axioms fiveSite_finiteCharacterFamily_secondOrder_contract
#print axioms fiveSite_finiteCharacterFamily_firstOrder_contract
#print axioms fiveSite_finiteCharacterFamily_fullMoment_contract

end

end ArchonPhysicsConsumers.Thermalization.FiniteSecondOrderCharacterFamilyExpansion

import ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound

/-!
Consumer for the exact and quantitative twist-difference analysis of the
physical iterated/iterated second-Picard remainder.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example (outer inner time : Real) :
    nestedOscillatoryClosedForm outer inner time =
      nestedOscillatoryIntegral outer inner time :=
  nestedOscillatoryClosedForm_eq outer inner time

example (outer inner : Real) :
    Continuous (nestedOscillatoryClosedForm outer inner) :=
  continuous_nestedOscillatoryClosedForm_time outer inner

example (time : Real) :
    Continuous (fun p : Real × Real =>
      nestedOscillatoryIntegral p.1 p.2 time) :=
  continuous_nestedOscillatoryIntegral_mismatches time

example (gamma outer inner outerTwist innerTwist time : Real) :
    nestedTwistDifference outer inner outerTwist innerTwist time =
      nestedTwistGoodPart gamma outer inner outerTwist innerTwist time +
        nestedTwistBadPart gamma outer inner outerTwist innerTwist time :=
  nestedTwistDifference_eq_goodPart_add_badPart
    gamma outer inner outerTwist innerTwist time

example {gamma outer inner outerTwist innerTwist time : Real}
    (hgamma : 0 < gamma)
    (htotal : outer + inner = outerTwist + innerTwist)
    (hgood : NestedTwistGood gamma outer inner outerTwist innerTwist) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      8 / gamma ^ 2 :=
  norm_nestedTwistDifference_le_eight_div_sq hgamma htotal hgood

example (gamma outer inner outerTwist innerTwist time : Real) :
    ‖nestedTwistBadPart gamma outer inner outerTwist innerTwist time‖ ≤
      2 * |time| ^ 2 :=
  norm_nestedTwistBadPart_le_two_mul_abs_time_sq
    gamma outer inner outerTwist innerTwist time

example :
    NestedTwistGood 1 1 1 3 (-1) ∧
      (1 : Real) + 1 = 3 + (-1) ∧
      nestedTwistDifference 1 1 3 (-1) Real.pi ≠ 0 :=
  nestedTwistDifference_unitGood_obstruction

example {constant gamma outer inner outerTwist innerTwist time : Real}
    (hconstant : 0 ≤ constant) (hgamma : 0 < gamma)
    (hinner : gamma ≤ |inner|)
    (hinnerTwist : gamma ≤ |innerTwist|)
    (htotal : outer + inner = outerTwist + innerTwist)
    (hgain : NestedTwistNumeratorGain constant gamma
      outer inner outerTwist innerTwist time) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      constant / gamma :=
  norm_nestedTwistDifference_le_constant_div hconstant hgamma
    hinner hinnerTwist htotal hgain

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterMismatch m observed term +
        iteratedQuadraticInnerMismatch m term =
      iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term) +
        iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term) :=
  physicalIteratedA2_totalMismatch_flip_eq m observed term

example {N : Nat} [NeZero N] {constant gamma : Real}
    (hconstant : 0 ≤ constant) (hgamma : 0 < gamma)
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real)
    (hbound : ∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      ‖nestedTwistDifference
          (iteratedQuadraticOuterMismatch m observed term)
          (iteratedQuadraticInnerMismatch m term)
          (iteratedQuadraticOuterMismatch m observed
            (flipIteratedQuadraticInnerBranch term))
          (iteratedQuadraticInnerMismatch m
            (flipIteratedQuadraticInnerBranch term)) time‖ ≤
        constant / gamma) :
    |completeA2IteratedIteratedRemainder
        m kappa radius observed time| ≤
      (1 / 4 : Real) *
        ((constant / gamma) *
          physicalIteratedA2StaticAbsMass
            m kappa radius observed) ^ 2 :=
  abs_completeA2IteratedIteratedRemainder_le_of_uniformTwistGain
    hconstant hgamma m kappa radius observed time hbound

example :
    ¬ ∃ alpha, CutoffExponentAdmissible 4 3
      quadraticKineticDeficit alpha :=
  generic_rankThree_g4_still_has_no_cutoff

example :
    CutoffExponentAdmissible 4 2 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent :=
  numeratorGain_lossTwo_cutoff_admissible

end

end ArchonPhysicsConsumers.Thermalization

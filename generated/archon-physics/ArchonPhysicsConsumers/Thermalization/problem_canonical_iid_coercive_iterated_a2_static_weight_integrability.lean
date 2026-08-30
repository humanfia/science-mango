import ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability

/-!
Consumer check for the fixed-volume actual iterated-A2 static-weight ceiling
and integrability theorem.
-/

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

example
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) :
    ‖actualIteratedA2StaticWeightSample ensemble kappa radius observed term
        sample‖ <=
      4 * |kappa| ^ 2 * R ^ 3 :=
  norm_actualIteratedA2StaticWeightSample_le ensemble kappa R hR radius
    hradius observed term sample

example
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hweight : Measurable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)) :
    Integrable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      ensemble.probability :=
  integrable_actualIteratedA2StaticWeightSample ensemble kappa R hR radius
    hradius observed term hweight

#print axioms abs_interactionTensor_three_le_five_mul_firstFrequency
#print axioms norm_firstPicardCoordinateBranchStaticCoefficient_le
#print axioms norm_outerCoupling_mul_interactionTensor_le_eight_absKappa
#print axioms norm_iteratedQuadraticSecondPicardStaticCoefficient_le
#print axioms norm_actualIteratedA2StaticWeightSample_le
#print axioms integrable_actualIteratedA2StaticWeightSample

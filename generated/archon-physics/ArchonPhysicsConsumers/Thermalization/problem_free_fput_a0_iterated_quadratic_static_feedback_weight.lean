import ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
import ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

/-!
# Consumer: explicit physical A0/A2 return-tree weight

This consumer connects the expanded physical formula to the static feedback
weight used by the finite-time broadening theorem.  It exposes the guarded
all-frequency identity, the compact positive-frequency formula, and the
energy-normalized squared identity with two separate three-leg interaction
weights.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticStaticFeedbackWeight
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderFiniteTimeBroadeningFormula

noncomputable section

/-- Consumer endpoint for the exact guarded physical expansion of the static
return-tree feedback weight. -/
theorem problem_iteratedQuadraticFeedbackStaticWeight_eq_guardedExpanded
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticFeedbackStaticWeight
        m kappa radius observed term =
      if 0 < modeFrequency m observed ∧
          0 < modeFrequency m (iteratedQuadraticFirstPicardMode term) then
        iteratedQuadraticExpandedStaticFeedbackWeight
          m kappa radius observed term
      else 0 := by
  unfold iteratedQuadraticFeedbackStaticWeight
  exact
    re_freeInitial_mul_star_iteratedStaticCoefficient_eq_guardedExpanded
      m kappa radius observed term

/-- Consumer endpoint for the compact signed positive-frequency formula. -/
theorem problem_iteratedQuadraticFeedbackStaticWeight_eq_compact_of_pos
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hObserved : 0 < modeFrequency m observed)
    (hInner : 0 < modeFrequency m
      (iteratedQuadraticFirstPicardMode term)) :
    iteratedQuadraticFeedbackStaticWeight
        m kappa radius observed term =
      -firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 * kappa ^ 2 *
        interactionTensor m 3
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        interactionTensor m 3
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        radius observed * radius (iteratedQuadraticFreeMode term) *
        radius ((iteratedQuadraticInnerEntry term).1.1 0) *
        radius ((iteratedQuadraticInnerEntry term).1.1 1) /
        (32 * modeFrequency m
          (iteratedQuadraticFirstPicardMode term)) := by
  unfold iteratedQuadraticFeedbackStaticWeight
  exact
    re_freeInitial_mul_star_iteratedStaticCoefficient_eq_compact_of_pos
      m kappa radius observed term hObserved hInner

/-- Consumer endpoint for the exact action/normalized-weight identity.  The
square removes only the branch sign; it does not assume a gain/loss sign for
the unsquared feedback. -/
theorem problem_sq_iteratedQuadraticFeedbackStaticWeight_phaseEnergyRadius_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hOuterPositive : PositiveModeTuple m
      (Fin.cons observed (iteratedQuadraticOuterModes term)))
    (hInnerPositive : PositiveModeTuple m
      (Fin.cons (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term).1.1)) :
    (iteratedQuadraticFeedbackStaticWeight m kappa
      (phaseEnergyRadius energy (modeFrequency m)) observed term) ^ 2 =
      kappa ^ 4 *
        normalizedInteractionWeight m
          (Fin.cons observed (iteratedQuadraticOuterModes term)) *
        normalizedInteractionWeight m
          (Fin.cons (iteratedQuadraticFirstPicardMode term)
            (iteratedQuadraticInnerEntry term).1.1) *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m)
          (iteratedQuadraticFreeMode term) *
        modeAction energy (modeFrequency m)
          ((iteratedQuadraticInnerEntry term).1.1 0) *
        modeAction energy (modeFrequency m)
          ((iteratedQuadraticInnerEntry term).1.1 1) := by
  unfold iteratedQuadraticFeedbackStaticWeight
  exact
    sq_re_freeInitial_mul_star_iteratedStaticCoefficient_phaseEnergyRadius_eq
      m kappa energy observed term hEnergy hOuterPositive hInnerPositive

#print axioms
  problem_iteratedQuadraticFeedbackStaticWeight_eq_guardedExpanded
#print axioms
  problem_iteratedQuadraticFeedbackStaticWeight_eq_compact_of_pos
#print axioms
  problem_sq_iteratedQuadraticFeedbackStaticWeight_phaseEnergyRadius_eq

end

end ArchonPhysicsConsumers.Thermalization

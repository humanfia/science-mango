import ArchonPhysics.FrozenRandomMassHardModeEFCBridge

/-!
# Consumer: actual frozen random-mass hard-mode EFC

This consumer replays the public actual-to-generic and
eigenvector-to-projector bridges, the sharp universal annealed bound, the
frozen one-site small-ball input, and the precise projector-contraction
reduction left for spatial localization.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli
open ArchonPhysics.FrozenRandomMassHardModeEFCBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory
open ArchonPhysics.OrderedSingleModeProjector
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

example (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y =
      hardEigenfunctionCorrelator
        (frozenRandomMassHardMode ensemble alpha)
        (frozenRandomMassEigenvectorCoordinate ensemble)
        n omega x y :=
  frozenRandomMassHardModeEFC_eq_hardEigenfunctionCorrelator
    ensemble alpha n omega x y

example (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2))
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y =
      frozenRandomMassHardModeProjectorEFC
        ensemble alpha n omega x y :=
  frozenRandomMassHardModeEFC_eq_projectorEFC_of_simple
    ensemble alpha n omega x y hsimple

example (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2))
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y <= 1 :=
  frozenRandomMassHardModeEFC_le_one_of_simple
    ensemble alpha n omega x y hsimple

example (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (x y : Fin (n + 2)) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      ensemble alpha n omega x y ∂ensemble.probability) <= 1 :=
  lintegral_frozenRandomMassHardModeEFC_le_one ensemble alpha n x y

example (alpha : Real) (n : Nat) (x y : Fin (n + 2)) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      canonicalIIDMassPhaseEnsemble alpha n omega x y
      ∂(RandomEnsemble.canonicalLaw)) <= 1 :=
  canonical_lintegral_frozenRandomMassHardModeEFC_le_one alpha n x y

example {lambda a b : Real} (hlambda : lambda ≠ 0) :
    RandomMassAndersonTransferBridge.andersonDiagonalPotentialLaw lambda
        (Set.Icc a b) <=
      ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) *
        ENNReal.ofReal (b - a) :=
  frozenDiagonalPotentialSmallBall_le hlambda

example (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real) (n : Nat)
    (x y : Fin (n + 2)) (bound : ENNReal)
    (hcontraction :
      (∫⁻ omega, frozenRandomMassHardModeProjectorEFC
        ensemble alpha n omega x y ∂ensemble.probability) <= bound) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      ensemble alpha n omega x y ∂ensemble.probability) <= bound :=
  lintegral_frozenRandomMassHardModeEFC_le_of_projectorContraction
    ensemble alpha n x y bound hcontraction

#print axioms frozenRandomMassHardModeEFC_eq_hardEigenfunctionCorrelator
#print axioms frozenRandomMassHardModeEFC_eq_projectorEFC_of_simple
#print axioms sum_sq_frozenRandomMassEigenvectorCoordinate_eq_one_of_simple
#print axioms frozenRandomMassHardModeEFC_le_one_of_simple
#print axioms frozenRandomMassHardModeEFC_le_one_ae
#print axioms lintegral_frozenRandomMassHardModeEFC_le_one
#print axioms canonical_lintegral_frozenRandomMassHardModeEFC_le_one
#print axioms frozenDiagonalPotentialSmallBall_le
#print axioms lintegral_frozenRandomMassHardModeEFC_le_of_projectorContraction

end

end ArchonPhysicsConsumers.Thermalization

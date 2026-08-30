import ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual

/-!
# Consumer: localized block modes as physical periodic-chain quasimodes
-/

open scoped Matrix

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.PeriodicWeightedCycleLocalizedQuasimodeResidual

noncomputable section

/-- A local eigenvector enters the genuinely coupled chain through exactly
four scalar cut-bond overlaps. -/
theorem problem_periodic_leftBlockEigenvector_residual_eq_fourOverlaps
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v) :
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v -
        lambda • leftZeroExtension v =
      ∑ r : Fin 4,
        (boundaryCoefficients (n := n) (m := m) w r *
          (boundaryVectors (n := n) (m := m) r ⬝ᵥ
            leftZeroExtension v)) •
          boundaryVectors (n := n) (m := m) r :=
  splitFinWeightedCycle_leftEigenvector_residual_eq_overlapSum
    w v lambda hv

/-- Exact cut orthogonality is the zero-error endpoint of the localization
bridge. -/
theorem problem_periodic_leftBlockEigenvector_of_cutOrthogonal
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (w : Fin (n + m) → Real) (v : Fin n → Real) (lambda : Real)
    (hv :
      (finWeightedCycleHermitian (leftWeights w)).1 *ᵥ v = lambda • v)
    (hcut : ∀ r : Fin 4,
      boundaryVectors (n := n) (m := m) r ⬝ᵥ
        leftZeroExtension v = 0) :
    (splitFinWeightedCycleHermitian w).1 *ᵥ leftZeroExtension v =
      lambda • leftZeroExtension v :=
  splitFinWeightedCycle_mulVec_leftEigenvector_of_boundaryOrthogonal
    w v lambda hv hcut

#print axioms
  problem_periodic_leftBlockEigenvector_residual_eq_fourOverlaps
#print axioms
  problem_periodic_leftBlockEigenvector_of_cutOrthogonal

end

end ArchonPhysicsConsumers.Thermalization

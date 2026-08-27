import ArchonPhysics.TruncatedGaussianFiniteEventTransfer

/-!
# Consumer: finite-volume uniform/Gaussian event transfer

This consumer checks the F3 ensemble adapter.  It records both the exact
tensorized lower comparison already available for truncated-Gaussian masses
and the reverse high-probability transfer under an explicit one-site RN upper
bound.  The latter retains the factor `constant ^ N`; no volume-uniform
change-of-law theorem is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.TruncatedGaussianFiniteEventTransfer
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.ConcreteGaussianTwoBandInitialEnsemble
open ArchonPhysics.TruncatedGaussianCoordinateUpperDomination
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Every finite event gets the exact tensorized lower-law comparison. -/
example (parameters : Parameters) (N : Nat)
    (event : Set (FiniteBlock N)) :
    exists density : NNReal, 0 < density /\
      (density : ENNReal) * uniformBlockLaw N event <=
        gaussianBlockLaw parameters N event :=
  exists_uniform_event_scaled_le_gaussian_event parameters N event

/-- A uniform failure estimate transfers to the Gaussian law only after it
beats the explicit exponential RN cost. -/
example (parameters : Parameters) (constant : ENNReal)
    (hone : coordinateLaw parameters <=
      constant • ArchonPhysics.RandomEnsemble.massCoordinateLaw)
    (N : Nat) (failure : Set (FiniteBlock N)) (epsilon : ENNReal)
    (hrate : constant ^ N * uniformBlockLaw N failure <= epsilon) :
    gaussianBlockLaw parameters N failure <= epsilon :=
  gaussian_failure_le_of_uniform_failure_beats_exponential
    parameters constant hone N failure epsilon hrate

/-- For the concrete mean-one variance-`1/100` truncated Gaussian, the reverse
RN constant is constructed rather than assumed.  It is finite, at least one,
and still appears as `constant ^ N`. -/
example (N : Nat) :
    ∃ constant : ENNReal, 1 <= constant ∧ constant ≠ ∞ ∧
      gaussianBlockLaw
          concreteMassParameters N <=
        constant ^ N • uniformBlockLaw N := by
  let parameters :=
    concreteMassParameters
  obtain ⟨constant, hone, hfinite, hdomination⟩ :=
    exists_finite_coordinateUpperConstant parameters
  exact ⟨constant, hone, hfinite,
    gaussianBlock_le_pow_smul_uniformBlock_of_coordinate_le
      parameters constant hdomination N⟩

#print axioms exists_finite_coordinateUpperConstant
#print axioms exists_gaussianBlock_le_pow_smul_uniformBlock

#print axioms exists_uniformBlock_smul_le_gaussianBlock
#print axioms gaussian_sample_failure_le_of_uniform_sample_failure_beats_exponential

end

end ArchonPhysicsConsumers.Thermalization

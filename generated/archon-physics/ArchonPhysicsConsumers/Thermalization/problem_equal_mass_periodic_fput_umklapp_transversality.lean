import ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

namespace ArchonPhysicsConsumers.Thermalization

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

theorem umklapp_k₂_derivative_factor_consumer
    (k₀ k₁ k₂ : Real) :
    deriv (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z) k₂ =
      -2 * Real.cos ((k₀ + k₁) / 4) *
        Real.cos ((2 * k₂ - k₀ - k₁) / 4) := by
  exact deriv_umklappReducedFourWaveMismatch_k₂ k₀ k₁ k₂

theorem umklapp_k₂_degeneracy_classification_consumer
    (k₀ k₁ k₂ : Real) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      Real.cos ((k₀ + k₁) / 4) = 0 ∨
        Real.cos ((2 * k₂ - k₀ - k₁) / 4) = 0 :=
  umklappK₂DerivativeDegenerate_iff_cosine_factor k₀ k₁ k₂

theorem umklapp_conditional_nearResonant_sliceDiameter_consumer
    {k₀ k₁ a b γ Δ x y : Real}
    (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (htransverse : UmklappK₂FixedSignTransverseOn k₀ k₁ a b γ)
    (hxIcc : x ∈ Icc a b) (hyIcc : y ∈ Icc a b)
    (hxnear : |umklappReducedFourWaveMismatch k₀ k₁ x| ≤ Δ)
    (hynear : |umklappReducedFourWaveMismatch k₀ k₁ y| ≤ Δ) :
    dist x y ≤ 2 * Δ / γ :=
  umklapp_nearResonant_pair_distance_le hγ hΔ htransverse
    hxIcc hyIcc hxnear hynear

#print axioms umklapp_k₂_derivative_factor_consumer
#print axioms umklapp_k₂_degeneracy_classification_consumer
#print axioms umklapp_conditional_nearResonant_sliceDiameter_consumer

end ArchonPhysicsConsumers.Thermalization

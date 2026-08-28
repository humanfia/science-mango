import ArchonPhysics.ProjectorWeightProfileCauchyBinetBridge

namespace ArchonPhysicsConsumers.Thermalization

open scoped Matrix

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ProjectorWeightProfileCauchyBinetBridge
open ArchonPhysics.SingleMassRankOnePerturbation
open ArchonPhysics.ThreeParameterProjectorWeightJacobian

noncomputable section

/-- Consumer-facing finite-dimensional Gram-to-injective-minor bridge. -/
theorem problem_exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin 3) ι Real)
    (hgram : (Q * Q.transpose).det ≠ 0) :
    ∃ sites : Fin 3 → ι, Function.Injective sites ∧
      (Q.submatrix id sites).det ≠ 0 :=
  exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero Q hgram

/-- Consumer-facing actual cycle-projector profile specialization. -/
theorem problem_exists_injective_cycleSites_projectorMinor_ne_zero_of_profileGram
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hgram :
      (orderedCycleProjectorWeightProfile A modes *
        (orderedCycleProjectorWeightProfile A modes).transpose).det ≠ 0) :
    ∃ sites : Fin 3 → Lattice.Site N, Function.Injective sites ∧
      (orderedProjectorWeightMatrix A modes
        (fun s => cycleMassPerturbationVector (sites s))).det ≠ 0 :=
  exists_injective_cycleSites_projectorMinor_ne_zero_of_profileGram_det_ne_zero
    A modes hgram

/-- Consumer-facing contrapositive: universal distinct-site minor collapse
forces collapse of the full actual projector-profile Gram determinant. -/
theorem problem_profileGram_det_eq_zero_of_all_injective_cycleSite_minors_zero
    {N : Nat} [NeZero N]
    (A : HermitianMatrix (Lattice.Site N))
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (hminor : ∀ sites : Fin 3 → Lattice.Site N,
      Function.Injective sites →
      (orderedProjectorWeightMatrix A modes
        (fun s => cycleMassPerturbationVector (sites s))).det = 0) :
    (orderedCycleProjectorWeightProfile A modes *
      (orderedCycleProjectorWeightProfile A modes).transpose).det = 0 :=
  profileGram_det_eq_zero_of_all_injective_cycleSite_projectorMinor_eq_zero
    A modes hminor

#print axioms problem_exists_injective_threeColumnMinor_ne_zero_of_gram_det_ne_zero
#print axioms problem_exists_injective_cycleSites_projectorMinor_ne_zero_of_profileGram
#print axioms problem_profileGram_det_eq_zero_of_all_injective_cycleSite_minors_zero

end

end ArchonPhysicsConsumers.Thermalization

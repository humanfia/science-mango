import ArchonPhysics.LennardJonesStoppedHigherRemainderProbability

/-!
# Consumer: stopped-flow probability bound for the higher LJ remainder
-/

namespace ArchonPhysicsConsumers.Thermalization.LennardJonesStoppedHigherRemainderProbability

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesStoppedHigherRemainderProbability

noncomputable section

/-- For the paper mass support `m_i >= 4/5`, the integrated higher LJ
remainder has a volume-independent `O(L * g)` all-mode RMS bound. -/
theorem paperMassSupport_accumulatedHigherResidualRMS_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualVector m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    kineticWindowAccumulatedHigherResidualRMS m depth r₀ g L q ≤
      higherRemainderRMSCoefficient (4 / 5 : Real)
        r₀ rho amplitudeBound * L * g := by
  exact kineticWindowAccumulatedHigherResidualRMS_le
    m (4 / 5 : Real) (by norm_num) hmass
      hdepth hr₀ hg hrho0 hrho1 hL hAmplitude q hIntegrable htube hamplitude

/-- The family-level interface exposes exactly the two remaining stochastic
inputs: a vanishing coupling and a vanishing good-event complement budget. -/
theorem problem_higherRemainder_tendstoInMeasure_zero
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    TendstoInMeasure probability error atTop (fun _omega => 0) := by
  exact certificate.tendstoInMeasure_zero
    probability coupling coefficient error hcoupling

#print axioms paperMassSupport_accumulatedHigherResidualRMS_le
#print axioms problem_higherRemainder_tendstoInMeasure_zero
#print axioms modalHigherResidualRMS_le_g_cubed
#print axioms kineticWindowAccumulatedHigherResidualRMS_le
#print axioms measureReal_accumulatedHigherResidual_tail_le_good_compl
#print axioms VanishingGoodEventRemainderCertificate.tendstoInMeasure_zero

end

end ArchonPhysicsConsumers.Thermalization.LennardJonesStoppedHigherRemainderProbability

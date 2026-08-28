import ArchonPhysics.CanonicalMarkedResonanceActionOnShellJointLimit

/-!
# Consumer: canonical marked resonance action on-shell joint limit

This consumer checks the complete scalar squared-sinc composition:

* fixed-coupling thermodynamic marked-kernel identification;
* the deterministic `Nmin(g)` diagonal cutoff;
* the inverse-square-time approximate identity; and
* extraction of a positive resonant cluster with its canonical signed
  Radon--Nikodym collision operator.

The density-at-zero premise remains explicit.
-/

open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization
open ArchonPhysics.CanonicalMarkedResonanceActionOnShellJointLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- Consumer-facing exact joint finite-volume squared-sinc action limit. -/
theorem problem_canonicalInverseSquareMarkedAction_jointOnShell
    (sign : Fin 3 -> InteractionSign)
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    (s : AdmissibleJointLimit
      (canonicalInverseSquareMarkedResonanceActionSizeCutoff sign)) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun j omega => canonicalMarkedResonanceActionSample sign
        inverseSquareKineticTime (s.coupling j) (s.systemSize j) omega)
      atTop (fun _omega => rho 0) :=
  canonicalInverseSquareMarkedResonanceAction_tendstoInMeasure_onShell_of_collisionDensity
    sign rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity s

/-- Consumer-facing positive-cluster and signed-RN endpoint. -/
theorem problem_exists_positive_inverseSquareOnShellCluster_with_rn
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    {coupling : Nat -> Real}
    (hcoupling_pos : forall j, 0 < coupling j)
    (hcoupling : Tendsto coupling atTop (nhdsWithin 0 (Ioi 0))) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                canonicalIIDMassPhaseEnsemble decayInteractionSign
                (inverseSquareKineticTime (coupling (subsequence j)))
                (inverseSquareKineticTime_pos
                  (hcoupling_pos (subsequence j))))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          collision.collisionMeasure.mass = Real.toNNReal (rho 0) /\
          collision.collisionMeasure ≠ 0 /\
          forall action : RankFrequencyMark -> Real,
            (collisionReferenceMeasure collision).withDensityᵥ
                (collisionVector collision action) =
              signedCollisionMeasure collision action :=
  exists_positive_canonicalInverseSquareOnShellMarkedCluster_with_rn_of_collisionDensity
    rho hrho_meas hrho_nonneg hrho_int hrho_zero hrho_pos hdensity
    hcoupling_pos hcoupling

#print axioms canonicalMarkedResonanceActionLimit_eq_markedBroadenedMass
#print axioms inverseSquareKineticTime_comp_tendsto_atTop
#print axioms canonicalInverseSquareMarkedResonanceActionLimit_tendsto_onShell_of_collisionDensity
#print axioms exists_positive_canonicalInverseSquareOnShellMarkedCluster_with_rn_of_collisionDensity
#print axioms problem_canonicalInverseSquareMarkedAction_jointOnShell
#print axioms problem_exists_positive_inverseSquareOnShellCluster_with_rn

end

end ArchonPhysicsConsumers.Thermalization

import ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization

/-!
# Consumer: exact marked resonance-action joint rate

This endpoint packages the deterministic cutoff for the canonical marked
squared-sinc action at inverse-square kinetic time.  It controls the tested
action directly and makes no quantitative claim about the weak-topology
pseudometric.
-/

open scoped Topology

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Topology

noncomputable section

/-- There is one deterministic volume cutoff such that:

* at every positive coupling `g`, volumes above the cutoff have probability
  less than `g` of an inverse-square-time action error at least `g`; and
* those bad-event probabilities tend to zero along every admitted joint
  weak-coupling/large-volume path.
-/
theorem exists_canonicalInverseSquareMarkedResonanceActionJointRate
    (sign : Fin 3 -> InteractionSign) :
    exists sizeCutoff : Real -> Nat,
      (forall {g : Real}, 0 < g -> forall {N : Nat},
        sizeCutoff g <= N ->
        RandomEnsemble.canonicalLaw.real
          {omega |
            g <= dist
              (canonicalMarkedResonanceActionSample sign
                inverseSquareKineticTime g N omega)
              (canonicalMarkedResonanceActionLimit sign
                inverseSquareKineticTime g)} < g) /\
      forall s : AdmissibleJointLimit sizeCutoff,
        Tendsto
          (fun j => RandomEnsemble.canonicalLaw.real
            {omega |
              s.coupling j <= dist
                (canonicalMarkedResonanceActionSample sign
                  inverseSquareKineticTime (s.coupling j)
                  (s.systemSize j) omega)
                (canonicalMarkedResonanceActionLimit sign
                  inverseSquareKineticTime (s.coupling j))})
          atTop (nhds 0) := by
  refine ⟨canonicalInverseSquareMarkedResonanceActionSizeCutoff sign,
    ?_, ?_⟩
  · intro g hg N hN
    exact canonicalMarkedResonanceActionBadEvent_probability_lt_of_cutoff
      sign inverseSquareKineticTime
      (fun _g hg' => inverseSquareKineticTime_pos hg') hg hN
  · intro s
    exact
      canonicalInverseSquareMarkedResonanceActionBadEvent_probability_jointLimit_tendsto_zero
        sign s

end

end ArchonPhysicsConsumers.Thermalization

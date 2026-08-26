import ArchonPhysics.CanonicalGlobalMeasurableFlow
import ArchonPhysics.JointMassEnergyCompactness
import ArchonPhysics.ParametricLocalHamiltonianFlow

/-!
# Global reduced-to-parameterized Hamiltonian flow adapter

The pointwise coercive trajectory lives in the mass-dependent subtype
`ReducedPhaseSpace m`, whereas the measurable canonical cutoff flow lives in
one fixed `ParametricPhaseSpace N`.  This file supplies the missing bridge.

A reduced point is first embedded with frozen reciprocal masses and coupling
parameters.  Energy conservation keeps every genuine reduced trajectory in a
joint mass--inverse-mass compact shell.  The continuous image of that shell
has one ambient norm bound, so the canonical cutoff flow agrees globally with
the embedded genuine trajectory by uniqueness.  No kinetic or thermalization
claim is made here.
-/

namespace ArchonPhysics.GlobalReducedParametricFlowAdapter

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianGlobalExistence
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.JointMassEnergyCompactness
open ArchonPhysics.CanonicalGlobalMeasurableFlow
open Set Metric

noncomputable section

variable {N : Nat} [NeZero N]

/-- A fixed-mass reduced point in the common parameter--phase space. -/
def embedReducedPoint
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (z : ReducedPhaseSpace m) : ParametricPhaseSpace N :=
  ((WithLp.toLp 2 fun i ↦ (m.mass i)⁻¹, (kappa, (beta, g))),
    ((z.1 : HilbertConfiguration N), (z.2 : HilbertConfiguration N)))

/-- The same reduced point with both mass and inverse-mass coordinates
retained, so that it can be placed in a joint compact energy shell. -/
def reducedJointPoint
    (m : Lattice.PositiveMassConfig N) (z : ReducedPhaseSpace m) :
    MassInversePhysicalPhaseSpace N :=
  ((m.mass, fun i ↦ (m.mass i)⁻¹),
    (asConfiguration (z.1 : HilbertConfiguration N),
      asConfiguration (z.2 : HilbertConfiguration N)))

/-- Forget the mass coordinate of a joint point and adjoin fixed coupling
parameters. -/
def jointPointToParametric (kappa beta g : Real) :
    MassInversePhysicalPhaseSpace N → ParametricPhaseSpace N :=
  fun x ↦
    ((WithLp.toLp 2 x.1.2, (kappa, (beta, g))),
      (WithLp.toLp 2 x.2.1, WithLp.toLp 2 x.2.2))

theorem continuous_jointPointToParametric (kappa beta g : Real) :
    Continuous (jointPointToParametric (N := N) kappa beta g) := by
  unfold jointPointToParametric
  fun_prop

@[simp] theorem jointPointToParametric_reducedJointPoint
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (z : ReducedPhaseSpace m) :
    jointPointToParametric kappa beta g (reducedJointPoint m z) =
      embedReducedPoint m kappa beta g z := by
  ext <;> rfl

/-- The retained mass and reciprocal-mass coordinates obey their exact
polynomial reciprocal constraint. -/
theorem reducedJointPoint_reciprocal
    (m : Lattice.PositiveMassConfig N) (z : ReducedPhaseSpace m)
    (i : Lattice.Site N) :
    (reducedJointPoint m z).1.1 i * (reducedJointPoint m z).1.2 i = 1 := by
  simp [reducedJointPoint, ne_of_gt (m.mass_pos i)]

/-- Both translation gauges are carried by the reduced subtypes. -/
theorem reducedJointPoint_gauges
    (m : Lattice.PositiveMassConfig N) (z : ReducedPhaseSpace m) :
    (∑ i, (reducedJointPoint m z).1.1 i *
      (reducedJointPoint m z).2.1 i) = 0 ∧
    (∑ i, (reducedJointPoint m z).2.2 i) = 0 := by
  constructor
  · simpa [reducedJointPoint, asConfiguration] using
      (mem_reducedPositionSpace_iff m
        (z.1 : HilbertConfiguration N)).1 z.1.property
  · simpa [reducedJointPoint, asConfiguration] using
      (mem_reducedMomentumSpace_iff
        (z.2 : HilbertConfiguration N)).1 z.2.property

/-- A reduced point of energy at most `H`, with masses in the prescribed
box, belongs to the corresponding joint compact shell. -/
theorem reducedJointPoint_mem_jointMassInverseEnergySublevel
    (m : Lattice.PositiveMassConfig N) (z : ReducedPhaseSpace m)
    (mLower mUpper uLower uUpper kappa beta g H : Real)
    (hmLower : ∀ i, mLower ≤ m.mass i)
    (hmUpper : ∀ i, m.mass i ≤ mUpper)
    (huLower : ∀ i, uLower ≤ (m.mass i)⁻¹)
    (huUpper : ∀ i, (m.mass i)⁻¹ ≤ uUpper)
    (henergy : reducedHamiltonian m kappa beta g z ≤ H) :
    reducedJointPoint m z ∈
      jointMassInverseEnergySublevel mLower mUpper uLower uUpper
        kappa beta g H := by
  refine ⟨?_, (reducedJointPoint_gauges m z).1,
    (reducedJointPoint_gauges m z).2, ?_⟩
  · intro i
    exact ⟨hmLower i, hmUpper i, huLower i, huUpper i,
      reducedJointPoint_reciprocal m z i⟩
  · rw [inverseMassHamiltonian_eq_hamiltonian_of_reciprocal
      m.mass_pos (fun i ↦ reducedJointPoint_reciprocal m z i)]
    exact henergy

/-- Embedding intertwines the reduced vector field with the common
parameterized Hamilton vector field. -/
theorem hasDerivAt_embedReducedPoint
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {z : Real → ReducedPhaseSpace m} {t : Real}
    (hz : HasDerivAt z (reducedVectorField m kappa beta g (z t)) t) :
    HasDerivAt (fun s ↦ embedReducedPoint m kappa beta g (z s))
      (parameterizedHamiltonVectorField
        (embedReducedPoint m kappa beta g (z t))) t := by
  have hqSub : HasDerivAt (fun s ↦ (z s).1)
      (reducedVelocity m (z t).2) t := by
    simpa [reducedVectorField] using
      hz.hasFDerivAt.fst.hasDerivAt
  have hpSub : HasDerivAt (fun s ↦ (z s).2)
      (-reducedPotentialGradient m kappa beta g (z t).1) t := by
    simpa [reducedVectorField] using
      hz.hasFDerivAt.snd.hasDerivAt
  have hq : HasDerivAt
      (fun s ↦ ((z s).1 : HilbertConfiguration N))
      ((reducedVelocity m (z t).2 : ReducedPositionSpace m) :
        HilbertConfiguration N) t :=
    (ReducedPositionSpace m).subtypeL.hasFDerivAt.comp_hasDerivAt t hqSub
  have hp : HasDerivAt
      (fun s ↦ ((z s).2 : HilbertConfiguration N))
      ((-reducedPotentialGradient m kappa beta g (z t).1 :
        ReducedMomentumSpace N) : HilbertConfiguration N) t :=
    (ReducedMomentumSpace N).subtypeL.hasFDerivAt.comp_hasDerivAt t hpSub
  have hparameters : HasDerivAt
      (fun _ : Real ↦
        (WithLp.toLp 2 fun i ↦ (m.mass i)⁻¹, (kappa, (beta, g)))) 0 t :=
    hasDerivAt_const t _
  have hphase := hq.prodMk hp
  have hall := hparameters.prodMk hphase
  have hfield :
      parameterizedHamiltonVectorField
        (embedReducedPoint m kappa beta g (z t)) =
        (0, MeasurableHamiltonianDynamics.explicitHamiltonVectorField
          m kappa beta g
          (((z t).1 : HilbertConfiguration N),
            ((z t).2 : HilbertConfiguration N))) := by
    apply Prod.ext
    · exact parameterizedHamiltonVectorField_parameters _
    · exact parameterizedHamiltonVectorField_phase_eq m kappa beta g _
  rw [hfield]
  simpa [embedReducedPoint,
    MeasurableHamiltonianDynamics.explicitHamiltonVectorField,
    reducedVelocity_coe, reducedPotentialGradient_coe] using hall

end

end ArchonPhysics.GlobalReducedParametricFlowAdapter

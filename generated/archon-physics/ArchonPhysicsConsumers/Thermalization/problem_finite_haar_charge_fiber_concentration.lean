import ArchonPhysics.FiniteHaarChargeFiberConcentration

/-!
Independent consumer for the arbitrary-finite-order Haar diagram
concentration bound.  A later Hamiltonian-to-kinetic expansion can discharge
the two visible inputs by bounding charge-fiber multiplicities and the square
mass of its deterministic diagram coefficients.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FiniteHaarChargeFiberConcentration
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact coherent-fiber second moment for an arbitrary finite diagram
family. -/
theorem problem_finiteHaarDiagram_exactSecondMoment
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int) :
    (∫ phase : UnitAddTorus d,
        Complex.normSq (finitePhaseCorrection coefficient charge phase)
        ∂finitePhaseHaarLaw d) =
      ∑ q ∈ realizedCharges charge,
        Complex.normSq (coherentFiberCoefficient charge coefficient q) :=
  integral_normSq_finitePhaseCorrection_eq_chargeFiberSum coefficient charge

/-- A uniform charge-fiber multiplicity bound controls the complete finite
Haar second moment without discarding coherent diagrams. -/
theorem problem_finiteHaarDiagram_secondMoment_le
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int)
    (multiplicity : Nat)
    (hmultiplicity : ∀ q ∈ realizedCharges charge,
      (chargeFiber charge q).card ≤ multiplicity) :
    (∫ phase : UnitAddTorus d,
        Complex.normSq (finitePhaseCorrection coefficient charge phase)
        ∂finitePhaseHaarLaw d) ≤
      multiplicity * ∑ j, Complex.normSq (coefficient j) :=
  integral_normSq_finitePhaseCorrection_le_of_fiberCard
    coefficient charge multiplicity hmultiplicity

/-- The same two deterministic diagram quantities give an explicit Haar
bad-event probability bound at every positive threshold. -/
theorem problem_finiteHaarDiagram_probability_le
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int)
    (multiplicity : Nat)
    (hmultiplicity : ∀ q ∈ realizedCharges charge,
      (chargeFiber charge q).card ≤ multiplicity)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    (finitePhaseHaarLaw d).real
        {phase | epsilon ≤
          ‖finitePhaseCorrection coefficient charge phase‖} ≤
      (multiplicity * ∑ j, Complex.normSq (coefficient j)) /
        epsilon ^ 2 :=
  measureReal_norm_ge_le_of_fiberCard
    coefficient charge multiplicity hmultiplicity hepsilon

#print axioms problem_finiteHaarDiagram_exactSecondMoment
#print axioms problem_finiteHaarDiagram_secondMoment_le
#print axioms problem_finiteHaarDiagram_probability_le

end

end ArchonPhysicsConsumers.Thermalization

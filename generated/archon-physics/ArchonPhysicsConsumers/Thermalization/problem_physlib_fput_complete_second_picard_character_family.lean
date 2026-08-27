import ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily

/-!
# Consumer: complete Physlib FPUT second-Picard character family

This consumer exposes the exact disjoint finite family for the full unit
second-Picard coefficient.  The left branch is the nested iterated-quadratic
tree; the right branch is the direct cubic oscillatory term with the physical
`beta` coupling.  No terms are grouped or omitted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

/-- The left branch retains exactly the nested iterated-quadratic coefficient
and its total initial-phase charge. -/
theorem problem_completeSecondPicard_iteratedBranch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    completeSecondPicardCoefficient m kappa beta radius observed time
        (Sum.inl term) =
        iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed time term ∧
      completeSecondPicardCharge (Sum.inl term) =
        iteratedQuadraticSecondPicardCharge term := by
  exact ⟨completeSecondPicardCoefficient_inl
      m kappa beta radius observed time term,
    completeSecondPicardCharge_inl term⟩

/-- The right branch retains exactly the direct cubic oscillatory coefficient
and cubic initial-phase charge; `beta` occurs in its physical unit coupling. -/
theorem problem_completeSecondPicard_directCubicBranch
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : CubicPhaseTerm N) :
    completeSecondPicardCoefficient m kappa beta radius observed time
        (Sum.inr term) =
        oscillatoryCoefficient
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (modeFrequency m observed) beta)
            m observed radius)
          (cubicPhaseMismatch (modeFrequency m) observed) time term ∧
      completeSecondPicardCharge (Sum.inr term) = cubicPhaseCharge term := by
  exact ⟨completeSecondPicardCoefficient_inr
      m kappa beta radius observed time term,
    completeSecondPicardCharge_inr term⟩

/-- The extracted P3 coefficient splits exactly into its integrated
iterated-quadratic and direct cubic components. -/
theorem problem_physlibFPUTSecondPicard_exactComponentSplit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time =
      physlibIteratedQuadraticSecondPicardCoefficient
          m kappa radius phase time observed +
        physlibFreeCubicSecondPicardCoefficient
          m beta observed radius phase time :=
  physlibFPUTSecondPicardCoefficient_eq_components
    m kappa beta radius phase time observed

/-- Consumer endpoint for the complete finite-character expansion of P3
`A2`. -/
theorem problem_physlibFPUTSecondPicard_exactCompleteCharacterFamily
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N) :
    physlibFPUTSecondPicardCoefficient
        m kappa beta observed radius phase time =
      finitePhaseCorrection
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase :=
  physlibFPUTSecondPicardCoefficient_eq_completeCharacterFamily
    m kappa beta radius phase time observed

/-- At zero observed frequency the complete family vanishes through the
physical tensor-decoupling endpoint. -/
theorem problem_completeSecondPicard_observedZeroDecoupling
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real)
    (phase : UnitAddTorus (Lattice.Site N)) (time : Real)
    (observed : Lattice.Site N)
    (hzero : modeFrequency m observed = 0) :
    finitePhaseCorrection
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge phase = 0 :=
  completeSecondPicardCharacterFamily_eq_zero_of_modeFrequency_eq_zero
    m kappa beta radius phase time observed hzero

#print axioms problem_completeSecondPicard_iteratedBranch
#print axioms problem_completeSecondPicard_directCubicBranch
#print axioms problem_physlibFPUTSecondPicard_exactComponentSplit
#print axioms problem_physlibFPUTSecondPicard_exactCompleteCharacterFamily
#print axioms problem_completeSecondPicard_observedZeroDecoupling

end

end ArchonPhysicsConsumers.Thermalization

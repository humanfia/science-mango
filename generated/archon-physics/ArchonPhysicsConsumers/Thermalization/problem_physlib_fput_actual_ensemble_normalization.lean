import ArchonPhysics.PhyslibFPUTActualEnsembleNormalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTActualEnsembleNormalization

noncomputable section

example {I Omega : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype Omega] [DecidableEq Omega]
    {N : Nat} [NeZero N]
    (weight : Omega -> Real)
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Omega -> Time -> HilbertConfiguration N)
    (hweight : ∑ omega, weight omega = 1)
    (time : Real) :
    actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q ∅ time = 1 := by
  exact actualFiniteCubicEnsembleBlockMoment_empty
    weight mass entry p q hweight time

#print axioms finiteWeightedBlockMoment_empty
#print axioms actualFiniteCubicEnsembleBlockMoment_empty

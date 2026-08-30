import ArchonPhysics.PhyslibFPUTActualEnsembleNormalization
import ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation

/-!
# Higher-order decoherence with uniformly bounded block moments

The ordered cluster telescope does not require each individual block moment
to converge.  At every fixed order it is enough that those moments are
uniformly bounded along the scaling sequence: a term tending to zero times a
bounded term still tends to zero.  This is the form naturally supplied by
coercive energy estimates.
-/

namespace ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation

open Filter
open Topology

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTActualEnsembleNormalization
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Arbitrary fixed-order factorization follows from prefix binary
factorization when the individual cluster moments are merely uniformly
bounded.  No limiting value for an individual moment is required. -/
theorem tendsto_orderedClusterFactorizationDefect_zero_of_uniformMomentBound
    (blockMoment : Nat -> Finset I -> Real -> Complex)
    (cluster : Nat -> Finset I) (time : Nat -> Real)
    (hempty : forall scale,
      blockMoment scale ∅ (time scale) = 1)
    (hbinary : forall level, Tendsto
      (fun scale => blockFactorizationDefect (blockMoment scale)
        (orderedClusterUnion cluster level) (cluster level) (time scale))
      atTop (nhds 0))
    (hmoment : forall level, exists bound : Real, forall scale,
      ‖blockMoment scale (cluster level) (time scale)‖ <= bound)
    (count : Nat) :
    Tendsto
      (fun scale => orderedClusterFactorizationDefect
        (blockMoment scale) cluster count (time scale))
      atTop (nhds 0) := by
  induction count with
  | zero =>
      have heq :
          (fun scale => orderedClusterFactorizationDefect
            (blockMoment scale) cluster 0 (time scale)) =
          (fun _ : Nat => (0 : Complex)) := by
        funext scale
        simp [orderedClusterFactorizationDefect, orderedClusterUnion,
          orderedClusterMomentProduct, hempty scale]
      rw [heq]
      exact tendsto_const_nhds
  | succ level ih =>
      have hbounded : IsBoundedUnder (fun x y : Real => x <= y) atTop
          (norm ∘ fun scale =>
            blockMoment scale (cluster level) (time scale)) := by
        rcases hmoment level with ⟨bound, hbound⟩
        exact Filter.isBoundedUnder_of ⟨bound, hbound⟩
      have hproduct : Tendsto
          (fun scale =>
            orderedClusterFactorizationDefect
                (blockMoment scale) cluster level (time scale) *
              blockMoment scale (cluster level) (time scale))
          atTop (nhds 0) :=
        ih.zero_mul_isBoundedUnder_le hbounded
      have hstep := (hbinary level).add hproduct
      simpa only [orderedClusterFactorizationDefect_succ,
        zero_add] using hstep

variable {Omega : Type*}
  [Fintype Omega] [DecidableEq Omega] [Nonempty I]

/-- Actual finite-ensemble specialization.  Weight normalization discharges
the empty block exactly; the only asymptotic inputs are prefix binary
decoherence and fixed-block uniform boundedness. -/
theorem actualFiniteCoerciveOrderedClusterFactorizationDefect_tendsto_zero_of_uniformMomentBound
    {N : Nat} [NeZero N]
    (weight : Omega -> Real)
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Nat -> Omega -> Time -> HilbertConfiguration N)
    (hweight : ∑ omega, weight omega = 1)
    (cluster : Nat -> Finset I)
    (time : Nat -> Real)
    (hbinary : forall level, Tendsto
      (fun scale => actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry (p scale) (q scale)
          (orderedClusterUnion cluster level) (cluster level) (time scale))
      atTop (nhds 0))
    (hmoment : forall level, exists bound : Real, forall scale,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry (p scale) (q scale) (cluster level)
          (time scale)‖ <= bound)
    (count : Nat) :
    Tendsto
      (fun scale => actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry (p scale) (q scale) cluster count (time scale))
      atTop (nhds 0) := by
  exact tendsto_orderedClusterFactorizationDefect_zero_of_uniformMomentBound
    (fun scale => actualFiniteCubicEnsembleBlockMoment
      weight mass entry (p scale) (q scale))
    cluster time
    (fun scale => actualFiniteCubicEnsembleBlockMoment_empty
      weight mass entry (p scale) (q scale) hweight (time scale))
    hbinary hmoment count

end

end ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation

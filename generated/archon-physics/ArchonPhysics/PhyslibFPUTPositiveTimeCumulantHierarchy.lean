import ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
import ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Exact positive-time moment and cumulant hierarchy for random-mass FPUT

This module proves the finite-order hierarchy identity which is available
before any kinetic closure.  For arbitrary finitely many signed slots, the
derivative of their joint monomial is the finite Leibniz sum obtained by
replacing one slot at a time by its exact source.  Finite weighted averages
of such monomials are genuine joint moments, and differentiating the usual
partition/Mobius formula gives the corresponding connected-cumulant
hierarchy.

For the high-order decoherence program, three logically different layers
must remain separate:

* the imported initial Haar selector is an exact t = 0 statement at every
  fixed finite order;
* this file supplies the exact t > 0 hierarchy along the same Hamiltonian
  orbit, again at every fixed finite order;
* charge-balanced, conservation-compatible, and genuinely resonant connected
  clusters are retained.  They are not declared to vanish.

What a kinetic-limit proof must still make small are the nonresonant,
recollision/repeated-index, and exceptional connected sectors.  Pairwise
decoherence alone does not imply this higher-order statement or RPA.
Deng--Hani's higher-statistics wave-kinetic hierarchy (arXiv:2110.04565) is a
blueprint for that separation, not a theorem imported here for random-mass
FPUT.


The final section instantiates every slot by the interaction-picture modal
amplitude of an actual differentiable Physlib trajectory.  The mass may vary
between the finitely many samples.  With `beta = 0`, the potential is
cubic-leading and the exact modal source is the verified quadratic tensor
source `physlibQuadraticRotatedSource`.  Thus the final derivative is exactly
"insert the actual quadratic source in one slot, then sum over partitions".

No random-phase assumption, positive-time independence, Markov property,
kinetic equation, cumulant decay, or closure is used.  In particular this is
an exact finite-dimensional hierarchy, not a proof that higher connected
cumulants become small.  Passing from the finite weighted ensemble below to
the continuous iid mass/Haar law additionally requires a justified
derivative-under-the-integral theorem (for example, a uniform integrable
derivative bound); that analytic step is deliberately not hidden here.
-/

namespace ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarConnectedCumulant
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

/-! ## Finite signed monomials and slot insertion -/

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Product of the positive-time signed paths in one finite block. -/
def signedBlockMonomial
    (path : I → Real → Complex) (block : Finset I) (time : Real) : Complex :=
  ∏ i ∈ block, path i time

/-- Exact Leibniz source: replace one slot of a block by its derivative and
retain all other slots. -/
def signedBlockSlotInsertion
    (path source : I → Real → Complex)
    (block : Finset I) (time : Real) : Complex :=
  ∑ i ∈ block,
    (∏ j ∈ block.erase i, path j time) * source i time

omit [Fintype I] [Nonempty I] in
/-- Arbitrary finite-order Leibniz identity for complex paths. -/
theorem hasDerivAt_signedBlockMonomial
    (path source : I → Real → Complex)
    (block : Finset I) (time : Real)
    (hpath : ∀ i ∈ block, HasDerivAt (path i) (source i time) time) :
    HasDerivAt (fun s ↦ signedBlockMonomial path block s)
      (signedBlockSlotInsertion path source block time) time := by
  simpa only [signedBlockMonomial, signedBlockSlotInsertion, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd hpath)

/-! ## Genuine finite weighted joint moments -/

/-- A finite weighted joint moment.  Nonnegative real weights summing to one
give an ordinary finite probability ensemble; normalization is not needed by
the differentiation identity. -/
def finiteWeightedBlockMoment
    (weight : Omega → Real) (path : Omega → I → Real → Complex)
    (block : Finset I) (time : Real) : Complex :=
  ∑ omega, (weight omega : Complex) *
    signedBlockMonomial (path omega) block time

/-- The corresponding finite weighted average of all one-slot source
insertions. -/
def finiteWeightedBlockInsertion
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (block : Finset I) (time : Real) : Complex :=
  ∑ omega, (weight omega : Complex) *
    signedBlockSlotInsertion (path omega) (source omega) block time

omit [DecidableEq Omega] in
/-- A finite weighted joint moment differentiates exactly to the finite
weighted one-slot insertion.  There is no measure-theoretic interchange
because the ensemble is finite. -/
theorem hasDerivAt_finiteWeightedBlockMoment
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (block : Finset I) (time : Real)
    (hpath : ∀ omega i, i ∈ block →
      HasDerivAt (path omega i) (source omega i time) time) :
    HasDerivAt
      (fun s ↦ finiteWeightedBlockMoment weight path block s)
      (finiteWeightedBlockInsertion weight path source block time) time := by
  unfold finiteWeightedBlockMoment finiteWeightedBlockInsertion
  apply HasDerivAt.fun_sum
  intro omega _homega
  exact (hasDerivAt_signedBlockMonomial
    (path omega) (source omega) block time
      (fun i hi ↦ hpath omega i hi)).const_mul (weight omega : Complex)

/-! ## Partition/Mobius connected-cumulant hierarchy -/

/-- A time-dependent supplied connected cumulant, using exactly the same
partition/Mobius convention as the initial Haar cumulant module. -/
def suppliedConnectedCumulantPath
    (blockMoment : Finset I → Real → Complex) (time : Real) : Complex :=
  suppliedJointCumulant (fun block ↦ blockMoment block time)

/-- The exact cumulant-hierarchy right-hand side.  For each partition, one
of its moment blocks is differentiated and all other block moments are
retained. -/
def suppliedConnectedCumulantHierarchySource
    (blockMoment blockSource : Finset I → Real → Complex)
    (time : Real) : Complex :=
  ∑ partition : Finpartition (Finset.univ : Finset I),
    partitionMobiusCoefficient partition *
      ∑ block ∈ partition.parts,
        (∏ other ∈ partition.parts.erase block,
          blockMoment other time) * blockSource block time

/-- Exact differentiation of the partition/Mobius formula.  This is the
unclosed connected-cumulant hierarchy: the theorem makes no assertion that
any source term vanishes or is small. -/
theorem hasDerivAt_suppliedConnectedCumulantPath
    (blockMoment blockSource : Finset I → Real → Complex)
    (time : Real)
    (hblock : ∀ block, HasDerivAt (blockMoment block)
      (blockSource block time) time) :
    HasDerivAt
      (fun s ↦ suppliedConnectedCumulantPath blockMoment s)
      (suppliedConnectedCumulantHierarchySource
        blockMoment blockSource time) time := by
  unfold suppliedConnectedCumulantPath suppliedJointCumulant
    suppliedConnectedCumulantHierarchySource
  apply HasDerivAt.fun_sum
  intro partition _hpartition
  have hproduct : HasDerivAt
      (fun s ↦ ∏ block ∈ partition.parts, blockMoment block s)
      (∑ block ∈ partition.parts,
        (∏ other ∈ partition.parts.erase block,
          blockMoment other time) * blockSource block time) time := by
    simpa only [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd
        (fun block _hblock ↦ hblock block))
  exact hproduct.const_mul (partitionMobiusCoefficient partition)

/-- Connected cumulant of the genuine finite weighted block moments. -/
def finiteWeightedConnectedCumulant
    (weight : Omega → Real) (path : Omega → I → Real → Complex)
    (time : Real) : Complex :=
  suppliedConnectedCumulantPath
    (finiteWeightedBlockMoment weight path) time

/-- Exact hierarchy source for a finite weighted connected cumulant. -/
def finiteWeightedConnectedCumulantHierarchySource
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (time : Real) : Complex :=
  suppliedConnectedCumulantHierarchySource
    (finiteWeightedBlockMoment weight path)
    (finiteWeightedBlockInsertion weight path source) time

/-- At arbitrary finite joint order, the derivative of the finite weighted
connected cumulant is exactly its partition sum of one-slot insertions. -/
theorem hasDerivAt_finiteWeightedConnectedCumulant
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (time : Real)
    (hpath : ∀ omega i,
      HasDerivAt (path omega i) (source omega i time) time) :
    HasDerivAt
      (fun s ↦ finiteWeightedConnectedCumulant weight path s)
      (finiteWeightedConnectedCumulantHierarchySource
        weight path source time) time := by
  apply hasDerivAt_suppliedConnectedCumulantPath
  intro block
  exact hasDerivAt_finiteWeightedBlockMoment
    weight path source block time (fun omega i _hi ↦ hpath omega i)

/-! ## Signed actual Physlib cubic-leading trajectories -/

/-- Positive-frequency interaction-picture amplitude of one actual
random-mass Physlib mode. -/
def physlibInteractionModePath
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) : Real → Complex :=
  fun time ↦ phaseRenormalize (modeFrequency m mode * time)
    (physlibModeAmplitude m mode p q time)

/-- Exact positive-frequency interaction-picture source in the
cubic-leading (`beta = 0`) random-mass FPUT Hamiltonian. -/
def physlibCubicLeadingQuadraticSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : Lattice.Site N) (q : Time → HilbertConfiguration N) :
    Real → Complex :=
  physlibModeRotatedSource m kappa 0 g mode q
/-- Pointwise bridge recording that the source below is the already verified
actual quadratic tensor source, not an abstract hierarchy placeholder. -/
@[simp] theorem physlibCubicLeadingQuadraticSource_eq_quadraticRotatedSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : Lattice.Site N) (q : Time → HilbertConfiguration N)
    (time : Real) :
    physlibCubicLeadingQuadraticSource m kappa g mode q time =
      physlibQuadraticRotatedSource m kappa g mode q time := rfl


/-- The actual Hamilton equation gives the exact quadratic source after the
free modal rotation. -/
theorem hasDerivAt_physlibInteractionModePath
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa 0 g p q)
    (homega : 0 < modeFrequency m mode) (time : Real) :
    HasDerivAt (physlibInteractionModePath m mode p q)
      (physlibCubicLeadingQuadraticSource m kappa g mode q time) time := by
  let source : Real → Complex :=
    physlibModeRotatedSource m kappa 0 g mode q
  have hcontinuous : Continuous source :=
    continuous_physlibModeRotatedSource m kappa 0 g mode q hq
  have hintegral : HasDerivAt
      (fun endpoint ↦ ∫ s in (0 : Real)..endpoint, source s)
      (source time) time :=
    intervalIntegral.integral_hasDerivAt_right
      (hcontinuous.intervalIntegrable (μ := MeasureTheory.volume) 0 time)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt
  have hrhs := hintegral.const_add (physlibModeAmplitude m mode p q 0)
  apply hrhs.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun endpoint ↦ by
    simpa only [physlibInteractionModePath, source] using
      (interactionPicture_physlibMode_eq_initial_add_integral_of_differentiable
        m kappa 0 g mode p q hp hq hHamilton homega endpoint)


/-- A phase/conjugate signed interaction-picture mode. -/
def signedPhyslibInteractionModePath
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (sign : PhaseSign)
    (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N) : Real → Complex :=
  fun time ↦ phaseSignActComplex sign
    (physlibInteractionModePath m mode p q time)

/-- The correspondingly signed exact quadratic source. -/
def signedPhyslibCubicLeadingQuadraticSource
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (sign : PhaseSign) (mode : Lattice.Site N)
    (q : Time → HilbertConfiguration N) : Real → Complex :=
  fun time ↦ phaseSignActComplex sign
    (physlibCubicLeadingQuadraticSource m kappa g mode q time)

/-- Complex conjugation commutes with the real-time derivative, so both
signed branches obey the correspondingly signed exact source equation. -/
theorem hasDerivAt_signedPhyslibInteractionModePath
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (sign : PhaseSign) (mode : Lattice.Site N)
    (p q : Time → HilbertConfiguration N)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa 0 g p q)
    (homega : 0 < modeFrequency m mode) (time : Real) :
    HasDerivAt (signedPhyslibInteractionModePath m sign mode p q)
      (signedPhyslibCubicLeadingQuadraticSource
        m kappa g sign mode q time) time := by
  have hpositive := hasDerivAt_physlibInteractionModePath
    m kappa g mode p q hp hq hHamilton homega time
  cases sign with
  | phase =>
      change HasDerivAt (physlibInteractionModePath m mode p q)
        (physlibCubicLeadingQuadraticSource m kappa g mode q time) time
      exact hpositive
  | conjugate =>
      change HasDerivAt
        (fun s ↦ star (physlibInteractionModePath m mode p q s))
        (star (physlibCubicLeadingQuadraticSource
          m kappa g mode q time)) time
      exact hpositive.star


/-! ## Actual finite random-mass ensemble adapter -/

/-- Signed mode path for one member of a finite ensemble of actual Physlib
trajectories.  Each member may carry a different positive mass realization. -/
def actualFiniteCubicEnsemblePath
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N) :
    Omega → I → Real → Complex :=
  fun omega i ↦ signedPhyslibInteractionModePath
    (mass omega) (entry i).1 (entry i).2 (p omega) (q omega)

/-- Exact signed quadratic source for the same finite ensemble. -/
def actualFiniteCubicEnsembleSource
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (q : Omega → Time → HilbertConfiguration N) :
    Omega → I → Real → Complex :=
  fun omega i ↦ signedPhyslibCubicLeadingQuadraticSource
    (mass omega) kappa g (entry i).1 (entry i).2 (q omega)

/-- Actual finite-ensemble signed joint moment. -/
def actualFiniteCubicEnsembleBlockMoment
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time : Real) : Complex :=
  finiteWeightedBlockMoment weight
    (actualFiniteCubicEnsemblePath mass entry p q) block time

/-- Actual finite-ensemble one-slot quadratic-source insertion. -/
def actualFiniteCubicEnsembleBlockInsertion
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (block : Finset I) (time : Real) : Complex :=
  finiteWeightedBlockInsertion weight
    (actualFiniteCubicEnsemblePath mass entry p q)
    (actualFiniteCubicEnsembleSource mass kappa g entry q) block time

/-- Every actual finite-ensemble joint moment satisfies the unclosed
one-slot quadratic-source hierarchy. -/
theorem hasDerivAt_actualFiniteCubicEnsembleBlockMoment
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa 0 g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (block : Finset I) (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q block s)
      (actualFiniteCubicEnsembleBlockInsertion
        weight mass kappa g entry p q block time) time := by
  apply hasDerivAt_finiteWeightedBlockMoment
  intro omega i _hi
  exact hasDerivAt_signedPhyslibInteractionModePath
    (mass omega) kappa g (entry i).1 (entry i).2
    (p omega) (q omega) (hp omega) (hq omega)
    (hHamilton omega) (homega omega i) time

/-- Connected cumulant of actual finite random-mass cubic-leading FPUT
trajectories. -/
def actualFiniteCubicEnsembleConnectedCumulant
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (time : Real) : Complex :=
  finiteWeightedConnectedCumulant weight
    (actualFiniteCubicEnsemblePath mass entry p q) time

/-- Exact partition/Mobius sum obtained by inserting the actual quadratic
source into one signed slot of one block. -/
def actualFiniteCubicEnsembleConnectedCumulantHierarchySource
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (time : Real) : Complex :=
  finiteWeightedConnectedCumulantHierarchySource weight
    (actualFiniteCubicEnsemblePath mass entry p q)
    (actualFiniteCubicEnsembleSource mass kappa g entry q) time

/-- Main actual-trajectory endpoint: at every positive or negative real
time and arbitrary finite joint order, the connected-cumulant derivative is
exactly the partition sum of one-slot insertions of the verified quadratic
Physlib source.  This is a hierarchy identity, not a closure or decay
estimate. -/
theorem hasDerivAt_actualFiniteCubicEnsembleConnectedCumulant
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa 0 g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCubicEnsembleConnectedCumulant
        weight mass entry p q s)
      (actualFiniteCubicEnsembleConnectedCumulantHierarchySource
        weight mass kappa g entry p q time) time := by
  apply hasDerivAt_finiteWeightedConnectedCumulant
  intro omega i
  exact hasDerivAt_signedPhyslibInteractionModePath
    (mass omega) kappa g (entry i).1 (entry i).2
    (p omega) (q omega) (hp omega) (hq omega)
    (hHamilton omega) (homega omega i) time

end

end ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

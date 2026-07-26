# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0989.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0989.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4b36c6f7e37e57687a088b2a885a10e4d378e0884aaf57dd4204d140379a0f17
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `electric Current Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `electric Potential Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.instZero` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Zero Electromagnetic Potential.** The electromagnetic potential in $d$ dimensions admits a zero element, defined as the potential that assigns the value zero to every point in its domain.
- `Electromagnetism.DistElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Distributional.ElectricField` | package PhysLean | The electric field of an electromagnetic potential which is a distribution.

### Query: `electrical Resistance Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.

### Query: `electrical Inductance Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.L𝓭_charge` | module `Physlib.Units.Dimension` | package PhysLean | **Electric Charge of the Length Dimension.** The electric charge component of the length dimension is zero.

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Voltage Quantity`
- `SM.SMNoGrav.One.linearParametersQENeqZero.tolinearParametersQNeqZero_v` | module `Physlib.Particles.StandardModel.AnomalyCancellation.NoGrav.One.LinearParameterization` | package PhysLean | **The Parameter $v$ of Linear Parameters with Non-zero $Q'$ and $E'$.** Given a set of linear parameters $S = (Q', Y, E')$ such that $Q' \neq 0$ and $E' \neq 0$, this definition provides the value of the rational para...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.

### Query: `Resistance Quantity`
- `UnitExamples.OddDimensions` | module `Physlib.Units.Examples` | package PhysLean | An example with complicated dimensions.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Inductance Quantity`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `Mathlib.Linter.Style.linter.style.induction` | module `Mathlib.Tactic.Linter.DeprecatedSyntaxLinter` | package Mathlib | The option `linter.style.induction` of the deprecated syntax linter flags usages of the `induction'` tactic, which is a backward-compatible version of Lean 3's `induction` tactic. Unlike Lean 4's `induction`, variable...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.instZero` (PhysLean)
- `Electromagnetism.DistElectromagneticPotential.electricField` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.C𝓭` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.L𝓭_charge` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `SM.SMNoGrav.One.linearParametersQENeqZero.tolinearParametersQNeqZero_v` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `UnitExamples.OddDimensions` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Mathlib.Linter.Style.linter.style.induction` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0989.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.CircuitComponent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.CircuitTopology`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.ComponentModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.DataMarker`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.ElectricCurrentQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.GraphAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.HasPhysicalSeriesRLParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.InductanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.IsUniqueMatchingAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.MatchesLongTimeStoredEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.MatchesStatedMeasurements`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.MatchesSuppliedVoltageTimeGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.MatchesWrittenScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.ResistanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.ResistorVoltageTimeGraph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.SatisfiesIdealSeriesRLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.SeriesSolenoidCircuit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.SwitchState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.TraceShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.VoltageQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0989.VoltmeterConnection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

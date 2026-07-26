# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0312.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0312.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ebe1995abffb5d120a16b8958b277258b5d134dec0af448135472eb6e0972137
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | The characteristic length `ξ` of the harmonic oscillator is defined as `√(ℏ /(m ω))`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Source Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.

### Query: `Acoustic Source Kind`
- `Mathlib.Tactic.Linarith.CompSource` | module `Mathlib.Tactic.Linarith.Oracle.FourierMotzkin` | package Mathlib | `CompSource` tracks the source of a comparison. The atomic source of a comparison is an assumption, indexed by a natural number. Two comparisons can be added to produce a new comparison, and one comparison can be scal...
- `stereographic_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the domain (source) of the stereographic projection associated with $v$ is the complement of the singleton set containing...
- `stereographic'_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For an $(n+1)$-dimensional real inner product space $E$ and a point $v$ on the unit sphere in $E$, the domain (source) of the stereographic projection from the sphere with p...

### Query: `Figure Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Source Separation Figure`
- `SeparationQuotient` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov quotient. This quotient is guaranteed to be a T₀ space.
- `r1_separation` | module `Mathlib.Topology.Separation.Basic` | package Mathlib | **Separation of Distinguishable Points in an $R_1$ Space.** In an $R_1$ topological space, if two points $x$ and $y$ are not inseparable, then there exist disjoint open sets $u$ and $v$ such that $x \in u$ and $y \in v$.
- `Equidecomp.apply_mem_target` | module `Mathlib.Algebra.Group.Action.Equidecomp` | package Mathlib | **Image of the Source under Equidecomposition.** For any equidecomposition $f$ and any point $x$ in its source, the image $f(x)$ is contained within the target of $f$.

### Query: `Two Point Source Interference Setup`
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.
- `Configuration.HasPoints` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of lines has an intersection point.
- `TwoP.of` | module `Mathlib.CategoryTheory.Category.TwoP` | package Mathlib | Turns a two-pointing into a two-pointed type.

## Grounded Mathlib/PhysLean names

- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `Mathlib.Tactic.Linarith.CompSource` (Mathlib)
- `stereographic_source` (Mathlib)
- `stereographic'_source` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `SeparationQuotient` (Mathlib)
- `r1_separation` (Mathlib)
- `Equidecomp.apply_mem_target` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Configuration.HasPoints` (Mathlib)
- `TwoP.of` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0312.AcousticSourceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.HasPhysicalLargeCircleParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.IsOddHalfWavelengthPathDifference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.IsUniqueMatchingAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.MatchesCoherentIsotropicSourceScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.MatchesDisplayedPointCount`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.MatchesSourceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.SatisfiesTwoPointSourceInterferenceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.SourceSeparationFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0312.TwoPointSourceInterferenceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0090.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0090.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:4b0263e00ca5b71230e16f4eca82a0c0c7744aed42084d46e79f3e968404051a
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

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

### Query: `Source Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...
- `Mathlib.Tactic.Monoidal.srcExpr` | module `Mathlib.Tactic.CategoryTheory.Monoidal.Datatypes` | package Mathlib | The domain of a morphism.

### Query: `Radiation Pattern`
- `SymbolicDynamics.FullShift.Pattern` | module `Mathlib.Dynamics.SymbolicDynamics.Basic` | package Mathlib | A *pattern* is a finite configuration in the full shift `A^G`. It consists of: * a full configuration `config : G → A` in the full shift; * a finite subset `support : Finset G` of coordinates, called the support of `p...
- `SymbolicDynamics.FullShift.Pattern.fromConfig` | module `Mathlib.Dynamics.SymbolicDynamics.Basic` | package Mathlib | Extract the finite pattern given by restricting a configuration `x : G → A` to a finite subset `U : Finset G`. The pattern has `config g = x g` for `g ∈ U` and `config g = default` outside `U`, with support `U`. In ot...
- `QuantumMechanics.radiusRegPowCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`.

### Query: `Screen Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Orientation.rotation_rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | Rotating twice is equivalent to rotating by the sum of the angles.

### Query: `Point Light Source`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `LightProfinite.instMetrizableSpaceOnePointNat` | module `Mathlib.Topology.Category.LightProfinite.Sequence` | package Mathlib | **Metrizability of the One-Point Compactification of the Natural Numbers.** The one-point compactification of the natural numbers $\mathbb{N}$ is a metrizable space.
- `Pointed` | module `Mathlib.CategoryTheory.Category.Pointed` | package Mathlib | The category of pointed types.

### Query: `Two Source Interference Setup`
- `Mathlib.Tactic.Linarith.CompSource` | module `Mathlib.Tactic.Linarith.Oracle.FourierMotzkin` | package Mathlib | `CompSource` tracks the source of a comparison. The atomic source of a comparison is an assumption, indexed by a natural number. Two comparisons can be added to produce a new comparison, and one comparison can be scal...
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `Stream'.interleave` | module `Mathlib.Data.Stream.Defs` | package Mathlib | Interleave two streams.

### Query: `common Wavelength`
- `Mathlib.Tactic.Ring.Common.Result` | module `Mathlib.Tactic.Ring.Common` | package Mathlib | The result of evaluating an (unnormalized) expression `e` into the type family `E` (typically one of `ExSum`, `ExProd`, `ExBase` or `BaseType`) is a (normalized) element `e'` and a representation `E e'` for it, and a...
- `Mathlib.Tactic.Ring.Common.ExSum` | module `Mathlib.Tactic.Ring.Common` | package Mathlib | `ExSum BaseType sα e` stores the structure of a normalized polynomial expression `e`, which is a sum of monomials.
- `SimpleGraph.walkLengthTwoEquivCommonNeighbors_apply_coe` | module `Mathlib.Combinatorics.SimpleGraph.Walk.Counting` | package Mathlib | **Equivalence of Length-Two Walks and Common Neighbors.** For any two vertices $u$ and $v$ in a simple graph $G$, there is a natural bijection between the set of walks of length 2 from $u$ to $v$ and the set of common...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `Mathlib.Tactic.Monoidal.srcExpr` (Mathlib)
- `SymbolicDynamics.FullShift.Pattern` (Mathlib)
- `SymbolicDynamics.FullShift.Pattern.fromConfig` (Mathlib)
- `QuantumMechanics.radiusRegPowCLM` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Orientation.rotation_rotation` (Mathlib)
- `LightProfinite` (Mathlib)
- `LightProfinite.instMetrizableSpaceOnePointNat` (Mathlib)
- `Pointed` (Mathlib)
- `Mathlib.Tactic.Linarith.CompSource` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `Stream'.interleave` (Mathlib)
- `Mathlib.Tactic.Ring.Common.Result` (Mathlib)
- `Mathlib.Tactic.Ring.Common.ExSum` (Mathlib)
- `SimpleGraph.walkLengthTwoEquivCommonNeighbors_apply_coe` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0090.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.EmitsInPhaseAtSameAmplitudeIsotropically`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.HasDepictedLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.HasPositivePhysicalLengths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.IsNearestDisplayedPathDifference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.PointLightSource`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.RadiationPattern`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.SatisfiesEuclideanRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.SatisfiesMonochromaticPropagationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.ScreenOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.SourceLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0090.TwoSourceInterferenceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

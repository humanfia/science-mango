# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0651.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0651.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:bf3c1edcaaea355dbcab2ce30344662d1666024a3bb941bf7db166dbdb998938
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `position Axis Unit`
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `Dimension.one_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length of the Unit Dimension.** The length component of the unit dimension is zero.

### Query: `Triangular Wavefunction Figure`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `Mathlib.Tactic.Widget.subTriangle` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Triangle with `homs = [f,g,h]` and `objs = [A,B,C]` ``` A f B h g C ```
- `Matrix.UpperTriangular` | module `Physlib.Mathematics.SchurTriangulation` | package PhysLean | The subtype of upper triangular matrices.

### Query: `Triangular Wavefunction Experiment`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `CategoryTheory.Triangulated.TStructure.triangleω₁δ_map_hom₁` | module `Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject` | package Mathlib | **The Spectral Triangle Functor.** Given a triangulated category $C$ equipped with a $t$-structure, there exists a functor from $C$ to the category of triangles in $C$ that assigns to each object its associated spectr...
- `Matrix.UpperTriangular` | module `Physlib.Mathematics.SchurTriangulation` | package PhysLean | The subtype of upper triangular matrices.

### Query: `probability Density Per Nanometre`
- `ProbabilityTheory.Kernel.density` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | Density of the kernel `κ` with respect to `ν`. This is a function `α → γ → Set β → ℝ` which is measurable on `α × γ` for all measurable sets `s : Set β` and satisfies that `∫ x in A, density κ ν a x s ∂(ν a) = (κ a).r...
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Position Probability Question`
- `ProbabilityTheory.mgf` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment-generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `ProbabilityTheory.Kernel` | module `Mathlib.Probability.Kernel.Defs` | package Mathlib | A kernel from a measurable space `α` to another measurable space `β` is a measurable function `κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by `MeasureTheory.Measure.instMea...

### Query: `Matches Supplied Triangular Wavefunction Figure`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `CategoryTheory.Triangulated.TStructure.triangleω₁δ_map_hom₁` | module `Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject` | package Mathlib | **The Spectral Triangle Functor.** Given a triangulated category $C$ equipped with a $t$-structure, there exists a functor from $C$ to the category of triangles in $C$ that assigns to each object its associated spectr...
- `Matrix.UpperTriangular` | module `Physlib.Mathematics.SchurTriangulation` | package PhysLean | The subtype of upper triangular matrices.

### Query: `Matches Stated Position Question`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `Mathlib.Tactic.ClickSuggestions.kabstractFindsPositions` | module `Mathlib.Tactic.ClickSuggestions.Util` | package Mathlib | Return whether `kabstract` uniquely finds pattern `p` in `e` at position `targetPos`.

### Query: `Satisfies Normalized Born Model`
- `Born` | module `Mathlib.Topology.Category.Born` | package Mathlib | The category of bornologies.
- `Born.instInhabited` | module `Mathlib.Topology.Category.Born` | package Mathlib | **Inhabitedness of the Category of Bornologies.** The type of all bornological spaces is inhabited, as it contains at least one element, specifically the bornology defined on the singleton set.
- `Born.instLargeCategory` | module `Mathlib.Topology.Category.Born` | package Mathlib | **The Category of Bornological Spaces.** The collection of bornological spaces forms a large category where the morphisms between any two objects are the locally bounded maps. In this category, the identity morphism f...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `IsUnit` (Mathlib)
- `Dimension.one_length` (PhysLean)
- `Matrix.BlockTriangular` (Mathlib)
- `Mathlib.Tactic.Widget.subTriangle` (Mathlib)
- `Matrix.UpperTriangular` (PhysLean)
- `Matrix.BlockTriangular` (Mathlib)
- `CategoryTheory.Triangulated.TStructure.triangleω₁δ_map_hom₁` (Mathlib)
- `Matrix.UpperTriangular` (PhysLean)
- `ProbabilityTheory.Kernel.density` (Mathlib)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `ProbabilityTheory.mgf` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `ProbabilityTheory.Kernel` (Mathlib)
- `Matrix.BlockTriangular` (Mathlib)
- `CategoryTheory.Triangulated.TStructure.triangleω₁δ_map_hom₁` (Mathlib)
- `Matrix.UpperTriangular` (PhysLean)
- `RegularExpression.matches'` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `Mathlib.Tactic.ClickSuggestions.kabstractFindsPositions` (Mathlib)
- `Born` (Mathlib)
- `Born.instInhabited` (Mathlib)
- `Born.instLargeCategory` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0651.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.IsUniqueClosestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.MatchesStatedPositionQuestion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.MatchesSuppliedTriangularWavefunctionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.PositionProbabilityQuestion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.RoundsToThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.SatisfiesNormalizedBornModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.TriangularWavefunctionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0651.TriangularWavefunctionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

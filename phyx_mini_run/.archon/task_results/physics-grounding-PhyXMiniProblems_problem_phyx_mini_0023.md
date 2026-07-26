# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0023.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0023.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length Real`
- `Real.dimH_univ` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | **Hausdorff Dimension of the Real Line.** The Hausdorff dimension of the set of all real numbers is equal to 1.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Dimension.L𝓭_length` | module `Physlib.Units.Dimension` | package PhysLean | **Length Dimension Component.** The length component of the fundamental physical dimension for length is equal to 1.

### Query: `Dim Time Real`
- `Time.rank_eq_one` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Dimension of the Time Space.** The rank of the real vector space of time durations is equal to one.
- `Real` | module `Mathlib.Data.Real.Basic` | package Mathlib | The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
- `Real.dimH_segment` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | The Hausdorff dimension of a non-degenerate segment in a real normed space is 1.

### Query: `Dim Speed Real`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `Real` | module `Mathlib.Data.Real.Basic` | package Mathlib | The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `nanosecond Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `UnitChoices.SIPrimed` | module `Physlib.Units.Basic` | package PhysLean | A `UnitChoices` which is related to `SI` by a prime scaling of each of the underlying units. This is useful in proving that a result is not dimensionally correct.
- `TimeUnit.nanoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of nanoseconds (10⁻⁹ of a second).

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `air Refractive Index`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `Composition.index` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | `c.index j` is the index of the block in the composition `c` containing `j`.
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `Rectangular Plastic Block`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `Matrix.fromBlocks` | module `Mathlib.Data.Matrix.Block` | package Mathlib | We can form a single large matrix by flattening smaller 'block' matrices of compatible dimensions.
- `Matrix.BlockTriangular.mul` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | **Product of Block Triangular Matrices.** If $M$ and $N$ are square matrices over a non-unital non-associative semiring that are block triangular with respect to a labeling function $b$ into a linear order, then their...

### Query: `Within Absolute Tolerance`
- `abs` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | `abs a`, denoted `|a|`, is the absolute value of `a`
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `WithAbs.norm_eq_abv` | module `Mathlib.Analysis.Normed.Ring.WithAbs` | package Mathlib | **Alias** of `WithAbs.norm_eq_apply_ofAbs`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.dimH_univ` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Dimension.L𝓭_length` (PhysLean)
- `Time.rank_eq_one` (PhysLean)
- `Real` (Mathlib)
- `Real.dimH_segment` (Mathlib)
- `DimSpeed` (PhysLean)
- `Real` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `UnitChoices` (PhysLean)
- `UnitChoices.SIPrimed` (PhysLean)
- `TimeUnit.nanoseconds` (PhysLean)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Subgroup.index` (Mathlib)
- `Composition.index` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `Matrix.BlockTriangular` (Mathlib)
- `Matrix.fromBlocks` (Mathlib)
- `Matrix.BlockTriangular.mul` (Mathlib)
- `abs` (Mathlib)
- `AbsoluteValue` (Mathlib)
- `WithAbs.norm_eq_abv` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0023.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.DimLengthReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.DimSpeedReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.DimTimeReal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.RectangularBlockTransitLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.RectangularPlasticBlock`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0023.WithinAbsoluteTolerance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

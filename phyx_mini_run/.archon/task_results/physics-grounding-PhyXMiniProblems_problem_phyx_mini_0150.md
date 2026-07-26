# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0150.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0150.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2d499ee9c94289eeec427aeeaa291d13a270ce3c3829845657b93d57665d2ed8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Value In`
- `LengthUnit.val_ne_zero` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Non-zero Length Unit.** For any length unit, its associated numerical value is non-zero.
- `LengthUnit.instInhabited` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Default Length Unit.** The type of length units is inhabited, with a default value defined as the positive real number $1$.
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `degree Readout`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` | module `Mathlib.Tactic.ComputeDegree` | package Mathlib | `miscomputedDegree? deg false_goals` takes as input * an `Expr`ession `deg`, representing the degree of a polynomial (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`); * a list of `MVarId`s `false_goal...
- `TuringDegree` | module `Mathlib.Computability.TuringDegree` | package Mathlib | Turing degrees are the equivalence classes of partial functions under Turing equivalence.

### Query: `Beam Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Prism Vertex`
- `VertexOperator` | module `Mathlib.Algebra.Vertex.VertexOperator` | package Mathlib | A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to Laurent series with coefficients in `V`. We write this as a specialization of the heterogeneous case.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PrincipalSeg.cocone_pt` | module `Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg` | package Mathlib | **Vertex of the Cocone for a Principal Segment.** Given a principal segment $f$ from a partially ordered set $\alpha$ to a partially ordered set $\beta$ and a functor $F$ from $\beta$ (viewed as a category) to a categ...

### Query: `Exit Angle Label`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | If the sign of the angle between three points is nonzero, the first and third points are not equal.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.val_ne_zero` (PhysLean)
- `LengthUnit.instInhabited` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Polynomial.degree` (Mathlib)
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` (Mathlib)
- `TuringDegree` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `StateT.mkLabel` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `VertexOperator` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PrincipalSeg.cocone_pt` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `EuclideanGeometry.left_ne_right_of_oangle_sign_ne_zero` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0150.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.BeamLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.ExitAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.HasSilicateFlintCalibration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.HasStatedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.IsPhysicalNormalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.MatchesDegreeReadoutToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.MatchesShownExitLabels`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.PrismExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.PrismRayAngles`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.PrismVertex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0150.SatisfiesPrismRayLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

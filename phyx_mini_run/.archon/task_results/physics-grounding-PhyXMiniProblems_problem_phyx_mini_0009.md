# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0009.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0009.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:17a3d35c29751ff705ce95baff8b7341c686f86f4a0e8074d9bfaefd870e7db0
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `radians Of Degrees`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Real.pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` | package Mathlib | The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from which one can derive all its properties. For explicit bounds on π, see `Mathlib/Analysis/Real/Pi/Bounds.lean`. Denoted `π`,...
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.

### Query: `degrees Of Radians`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees_add_of_disjoint` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of the Sum of Multivariate Polynomials with Disjoint Degrees.** For any two multivariate polynomials $p$ and $q$, if the multisets of their degrees are disjoint, then the degrees of their sum $p + q$ is equa...

### Query: `Triangular Glass Prism`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `SSet.horn.primitiveTriangle_coe` | module `Mathlib.AlgebraicTopology.SimplicialSet.Horn` | package Mathlib | **Primitive Triangle in a Horn.** For any natural number $n$, let $\Lambda^i_{n+3}$ be a horn of the standard $(n+3)$-simplex where the index $i$ satisfies $0 < i < n+3$. For any $k < n+2$, the primitive triangle is t...
- `Matrix.UpperTriangular` | module `Physlib.Mathematics.SchurTriangulation` | package PhysLean | The subtype of upper triangular matrices.

### Query: `Physically Valid`
- `Ordnode.Valid'` | module `Mathlib.Data.Ordmap.Ordset` | package Mathlib | The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are correct, the tree is balanced, and the elements of the tree are organized according to the ordering. This version of `Valid` als...
- `Ordnode.Valid'.valid` | module `Mathlib.Data.Ordmap.Ordset` | package Mathlib | **Validity of Bounded Ordered Nodes.** If an ordered tree is valid within a specific open interval $(o_1, o_2)$, then it is a valid ordered tree; that is, it satisfies the required balancing invariants, every node cor...
- `allFilePaths` | module `Physlib.Meta.AllFilePaths` | package PhysLean | Gets an array of all file paths in `Physlib`.

### Query: `Snell Law At Interface`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Law of sines** (sine rule), vector angle form.
- `EuclideanGeometry.law_sin` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | **Alias** of `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. --- **Law of sines** (sine rule), angle-at-point form.

### Query: `Is Principal Optical Angle`
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `top_isPrincipal` | module `Mathlib.RingTheory.PrincipalIdealDomain` | package Mathlib | **The Trivial Ideal is Principal.** In any semiring $R$, the top submodule of $R$ (the ring itself, considered as an ideal) is a principal ideal, as it is generated by the multiplicative identity $1$.
- `EuclideanGeometry.oangle_orthogonalProjection_self` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Projection` | package Mathlib | **Oriented Angle with an Orthogonal Projection.** Let $s$ be an affine subspace of an oriented Euclidean space, and let $p$ be a point not in $s$. Let $p'$ be a point in $s$ such that $p'$ is not equal to the orthogon...

### Query: `Prism Ray Path`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Quiver.Path.cast_rfl_rfl` | module `Mathlib.Combinatorics.Quiver.Cast` | package Mathlib | **Identity Path Casting.** For any path $p$ from a vertex $u$ to a vertex $v$ in a quiver, casting $p$ along the reflexivity proofs of $u = u$ and $v = v$ results in the original path $p$.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...

### Query: `Obeys Geometrical Optics`
- `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms` | module `Mathlib.AlgebraicGeometry.Geometrically.Basic` | package Mathlib | **Geometric Property under Isomorphism.** For a property of morphisms $P$ that is closed under isomorphisms, a morphism $f: X \to Y$ satisfies $P$ geometrically if and only if, for every field $K$ and every morphism $...
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `EuclideanGeometry.oangle_pointReflection_right` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | **Oriented Angle under Point Reflection of the Second Ray.** For any three points $p_1, p_2, p_3$ in a Euclidean geometry such that $p_1 \neq p_2$ and $p_3 \neq p_2$, the oriented angle $\measuredangle p_1 p_2 p_3'$ f...

### Query: `Can Emerge`
- `CanLift` | module `Mathlib.Tactic.Lift` | package Mathlib | A class specifying that you can lift elements from `α` to `β` assuming `cond` is true. Used by the tactic `lift`.
- `EReal.canLift` | module `Mathlib.Data.EReal.Basic` | package Mathlib | **Lifting Extended Reals to Reals.** An extended real number $x \in \overline{\mathbb{R}}$ can be lifted to a real number $r \in \mathbb{R}$ if and only if $x$ is neither positive infinity ($\infty$) nor negative infi...
- `Filter.canLift` | module `Mathlib.Order.Filter.Map` | package Mathlib | **Lifting Property for Filters.** If a type $\alpha$ can be lifted to a type $\beta$ via a map $c: \beta \to \alpha$ under a condition $p$, then the type of filters on $\alpha$ can be lifted to the type of filters on...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Real.pi` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees_add_of_disjoint` (Mathlib)
- `Matrix.BlockTriangular` (Mathlib)
- `SSet.horn.primitiveTriangle_coe` (Mathlib)
- `Matrix.UpperTriangular` (PhysLean)
- `Ordnode.Valid'` (Mathlib)
- `Ordnode.Valid'.valid` (Mathlib)
- `allFilePaths` (PhysLean)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `InnerProductGeometry.sin_angle_mul_norm_eq_sin_angle_mul_norm` (Mathlib)
- `EuclideanGeometry.law_sin` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `top_isPrincipal` (Mathlib)
- `EuclideanGeometry.oangle_orthogonalProjection_self` (Mathlib)
- `SameRay` (Mathlib)
- `Quiver.Path.cast_rfl_rfl` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `AlgebraicGeometry.geometrically_iff_of_isClosedUnderIsomorphisms` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `EuclideanGeometry.oangle_pointReflection_right` (Mathlib)
- `CanLift` (Mathlib)
- `EReal.canLift` (Mathlib)
- `Filter.canLift` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0009.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.CanEmerge`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.IsPrincipalOpticalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.PrismRayPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.PrismRayPath.ObeysGeometricalOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.RoundsToNearestTenthDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.SnellLawAtInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.TriangularGlassPrism`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0009.TriangularGlassPrism.PhysicallyValid`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

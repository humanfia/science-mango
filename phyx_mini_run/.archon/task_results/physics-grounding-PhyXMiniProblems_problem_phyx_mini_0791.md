# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0791.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0791.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d5d0ce52cfcfa3c9f4d6473ee923e981157327bec285d99085f6e89d856bd101
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Plane`
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `MSSMACC.planeY₃B₃` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3` | package PhysLean | The plane of linear solutions spanned by `Y₃`, `B₃` and `R`, a point orthogonal to `Y₃` and `B₃`.

### Query: `i Hat`
- `Complex.I` | module `Mathlib.Data.Complex.Basic` | package Mathlib | The imaginary unit.
- `iInf` | module `Mathlib.Order.SetNotation` | package Mathlib | Indexed infimum
- `iSup` | module `Mathlib.Order.SetNotation` | package Mathlib | Indexed supremum

### Query: `j Hat`
- `WeierstrassCurve.j` | module `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass` | package Mathlib | The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. Note that to prove two equal elliptic curves have the same `j`, you need to use `simp_rw`, as `rw` cannot transfer instance `We...
- `Matrix.crossProductMatrix_crossProductVee` | module `Physlib.Mathematics.CrossProductMatrix` | package PhysLean | On skew-symmetric matrices the hat map is also a right inverse of the vee map: if `Aᵀ = -A` then `[Aᵛ]ₓ = A`. Together with `crossProductVee_crossProductMatrix` this identifies `ℝ³` with the skew-symmetric `3 × 3` mat...
- `Matrix.J` | module `Mathlib.LinearAlgebra.SymplecticGroup` | package Mathlib | The matrix defining the canonical skew-symmetric bilinear form.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `direction At`
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `ContinuousAt` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A function between topological spaces is continuous at a point `x₀` if `f x` tends to `f x₀` when `x` tends to `x₀`.
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.

### Query: `Vector Diagram`
- `LightDiagram` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | A structure containing the data of sequential limit in `Profinite` of finite sets.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...

### Query: `Matches Problem And Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_pow` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Regular Expression Power and Kleene Star.** For any regular expression $P$, the language matched by the $n$-th power of $P$ is equal to the $n$-th power of the language matched by $P$. Similarly, the language matche...
- `RegularExpression.matches'_map` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | The language of the map is the map of the language.

### Query: `included Angle is Seventy Seven Degrees`
- `Real.Angle.toReal_le_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Upper Bound of the Real Representative of an Angle.** For any angle $\theta$, its representative in the interval $(-\pi, \pi]$ is always less than or equal to $\pi$.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Nat.weird_seventy` | module `Mathlib.NumberTheory.FactorisationProperties` | package Mathlib | **The Number 70 is Weird.** The natural number 70 is a weird number; that is, it is abundant but not pseudoperfect.

### Query: `scalar Product exact`
- `TensorProduct.finsuppScalarRight'` | module `Mathlib.LinearAlgebra.DirectSum.Finsupp` | package Mathlib | **Alias** of `TensorProduct.finsuppScalarRight`. --- The tensor product of `M` and `ι →₀ R` is linearly equivalent to `ι →₀ M`
- `IsScalarTower` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | An instance of `IsScalarTower M N α` states that the multiplicative action of `M` on `α` is determined by the multiplicative actions of `M` on `N` and `N` on `α`.
- `HasSum.smul` | module `Mathlib.Topology.Algebra.InfiniteSum.Module` | package Mathlib | **Sum of Scalar Products.** If a family of scalars $\{f_i\}_{i \in I}$ sums to $s$ and a family of vectors $\{g_j\}_{j \in J}$ sums to $t$, and if the family of all pairwise scalar products $\{f_i \cdot g_j\}_{(i, j)...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `MSSMACC.planeY₃B₃` (PhysLean)
- `Complex.I` (Mathlib)
- `iInf` (Mathlib)
- `iSup` (Mathlib)
- `WeierstrassCurve.j` (Mathlib)
- `Matrix.crossProductMatrix_crossProductVee` (PhysLean)
- `Matrix.J` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Space.Direction` (PhysLean)
- `ContinuousAt` (Mathlib)
- `Space.toDirection` (PhysLean)
- `LightDiagram` (Mathlib)
- `LightDiagram'` (Mathlib)
- `YoungDiagram` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_pow` (Mathlib)
- `RegularExpression.matches'_map` (Mathlib)
- `Real.Angle.toReal_le_pi` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Nat.weird_seventy` (Mathlib)
- `TensorProduct.finsuppScalarRight'` (Mathlib)
- `IsScalarTower` (Mathlib)
- `HasSum.smul` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0791.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0791.Plane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0791.VectorDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0146.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0146.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:87c41e2041a497ffc57f15cd44ee77bedb7ebf6edeb1a56281f1dc7bc79505d9
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `angle From Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)

### Query: `angle Degrees Readout`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Orientation.oangle_rotation_self_right` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A vector has an angle of `θ` from the rotation of that vector by `θ`.

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Prism Interface`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` | module `Mathlib.Tactic.Widget.LibraryRewrite` | package Mathlib | The structure with all data necessary for rendering a rewrite suggestion

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `Figure Angle Label`
- `Real.Angle.sign` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the sign of the sine of the angle.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are equal.

### Query: `incident Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SimpleGraph.edge_other_incident_set` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | **Incidence of an Edge at its Opposite Vertex.** If an edge $e$ is incident to a vertex $v$ in a simple graph $G$, then $e$ is also incident to the other vertex of $e$ relative to $v$.
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` | module `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | package Mathlib | **Middle Object of the Short Complex $L_2'$.** The middle object of the short complex $L_2'$ is defined as the first object of the short complex $L_3$ in the given snake input.

### Query: `transmitted Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Factorisation.terminal_mid` | module `Mathlib.CategoryTheory.Category.Factorisation` | package Mathlib | **Terminal Factorization Midpoint.** For a given morphism $f: X \to Y$, the intermediate object (or midpoint) of its terminal factorization is the codomain $Y$.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.

### Query: `Equilateral Glass Prism Diagram`
- `Affine.Simplex.Equilateral` | module `Mathlib.Analysis.Normed.Affine.Simplex` | package Mathlib | A simplex is equilateral if all the edge lengths are equal.
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...
- `CategoryTheory.Limits.WalkingReflexivePair` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | The type of objects for the diagram indexing reflexive (co)equalizers

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Orientation.oangle_rotation_self_right` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `Real.Angle.sign` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `SimpleGraph.edge_other_incident_set` (Mathlib)
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Factorisation.terminal_mid` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `Affine.Simplex.Equilateral` (Mathlib)
- `YoungDiagram` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0146.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.EquilateralGlassPrismDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.FigureAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.IsPhysicalRayAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.IsUniqueNearestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.ObeysSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.PrismInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.RoundsToNearestTenthDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.SatisfiesPrismRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0146.SatisfiesSnellsLawAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

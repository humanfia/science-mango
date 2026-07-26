# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0096.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0096.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:fb6fad2eaf448f874c24e55c657f0878362b9350749f21d821487853726d58eb
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Block Face`
- `MulAction.IsBlock` | module `Mathlib.GroupTheory.GroupAction.Blocks` | package Mathlib | A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint.
- `AddAction.IsBlock` | module `Mathlib.GroupTheory.GroupAction.Blocks` | package Mathlib | A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint.
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Face Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `PointedCone.IsFaceOf.isFaceOf_iff_le` | module `Mathlib.Geometry.Convex.Cone.Face.Basic` | package Mathlib | A face of a cone is a face of another if and only if they are contained in each other.

### Query: `Ray Travel Sense`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `face`
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.SimplicialObject.δ` | module `Mathlib.AlgebraicTopology.SimplicialObject.Basic` | package Mathlib | Face maps for a simplicial object.
- `PointedCone.IsFaceOf.isFaceOf_iff_le` | module `Mathlib.Geometry.Convex.Cone.Face.Basic` | package Mathlib | A face of a cone is a face of another if and only if they are contained in each other.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `degree Readout`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` | module `Mathlib.Tactic.ComputeDegree` | package Mathlib | `miscomputedDegree? deg false_goals` takes as input * an `Expr`ession `deg`, representing the degree of a polynomial (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`); * a list of `MVarId`s `false_goal...
- `TuringDegree` | module `Mathlib.Computability.TuringDegree` | package Mathlib | Turing degrees are the equivalence classes of partial functions under Turing equivalence.

### Query: `Transparent Block Setup`
- `Matrix.BlockTriangular` | module `Mathlib.LinearAlgebra.Matrix.Block` | package Mathlib | Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then `BlockTriangular M n b` says the matrix is block triangular.
- `AddAction.IsBlock.isBlockSystem` | module `Mathlib.GroupTheory.GroupAction.Blocks` | package Mathlib | Translates of a block form a block system
- `MulAction.IsBlock` | module `Mathlib.GroupTheory.GroupAction.Blocks` | package Mathlib | A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `MulAction.IsBlock` (Mathlib)
- `AddAction.IsBlock` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `PointedCone.IsFaceOf.isFaceOf_iff_le` (Mathlib)
- `SameRay` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `Module.Ray` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.SimplicialObject.δ` (Mathlib)
- `PointedCone.IsFaceOf.isFaceOf_iff_le` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Polynomial.degree` (Mathlib)
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` (Mathlib)
- `TuringDegree` (Mathlib)
- `Matrix.BlockTriangular` (Mathlib)
- `AddAction.IsBlock.isBlockSystem` (Mathlib)
- `MulAction.IsBlock` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0096.AdmissibleTIRIncidenceRadians`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.BlockFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.BlockRayPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.FaceOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.FollowsDepictedRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.HasDepictedBlockLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.HasPhysicalRayAngles`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.IsPhysicalNormalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.IsStrictlyAcuteNormalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.MatchesDisplayedAngleWithinSourceTolerance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.RayTravelSense`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.SatisfiesCriticalAngleSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.SatisfiesEntrySnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.SatisfiesPerpendicularFaceGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.TransparentBlockSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0096.UndergoesTotalInternalReflectionAtA`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

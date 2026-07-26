# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0001.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0001.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:1acbc8c73489d72f94a23453d0ceeb498a082acf01a84922c1be96bc66ed4366
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

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` | module `Mathlib.CategoryTheory.Abelian.Preradical.Colon` | package Mathlib | **The Middle Object of the Short Complex Associated with a Preradical.** For any object $X$ in a category $\mathcal{C}$, the middle object (at index 2) of the short complex associated with a preradical is defined as t...

### Query: `Diagram Plane`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.

### Query: `Air Water Refraction Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Equiv.pointReflection_apply` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | **Point Reflection Formula.** For any two points $x$ and $y$ in an affine space, the reflection of $y$ across the center $x$ is given by adding the displacement vector from $y$ to $x$ to the point $x$.
- `AffineEquiv.pointReflection_apply` | module `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv` | package Mathlib | **Point Reflection Formula.** For any points $x$ and $y$ in an affine space, the reflection of $y$ across the center $x$ is given by adding the displacement vector from $y$ to $x$ to the point $x$.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `degree Readout`
- `Polynomial.degree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`. `degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise `degree 0 = ⊥`.
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` | module `Mathlib.Tactic.ComputeDegree` | package Mathlib | `miscomputedDegree? deg false_goals` takes as input * an `Expr`ession `deg`, representing the degree of a polynomial (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`); * a list of `MVarId`s `false_goal...
- `TuringDegree` | module `Mathlib.Computability.TuringDegree` | package Mathlib | Turing degrees are the equivalence classes of partial functions under Turing equivalence.

### Query: `theta One`
- `Asymptotics.IsTheta` | module `Mathlib.Analysis.Asymptotics.Defs` | package Mathlib | We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and `g =O[l] f`.
- `Chebyshev.theta_one` | module `Mathlib.NumberTheory.Chebyshev` | package Mathlib | **Value of Chebyshev's Theta Function at One.** Chebyshev's $\theta$ function evaluated at $1$ is equal to $0$.
- `jacobiTheta_eq_jacobiTheta₂` | module `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` | package Mathlib | **Relationship between Jacobi Theta Functions.** For any complex number $\tau$, the Jacobi theta function $\theta(\tau)$ is equal to the two-variable Jacobi theta function $\theta(z, \tau)$ evaluated at $z = 0$.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Equiv.pointReflection_apply` (Mathlib)
- `AffineEquiv.pointReflection_apply` (Mathlib)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `Polynomial.degree` (Mathlib)
- `Mathlib.Tactic.ComputeDegree.miscomputedDegree?` (Mathlib)
- `TuringDegree` (Mathlib)
- `Asymptotics.IsTheta` (Mathlib)
- `Chebyshev.theta_one` (Mathlib)
- `jacobiTheta_eq_jacobiTheta₂` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0001.AirWaterRefractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.DiagramPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.HasPositiveRefractiveIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.IsPhysicalRefractionAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0001.SatisfiesSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

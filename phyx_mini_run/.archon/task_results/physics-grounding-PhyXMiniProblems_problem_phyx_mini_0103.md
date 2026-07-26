# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0103.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0103.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:0bca513af971f26f24e9a84587c21aa1e7146d24453a51b701a28315a439e4a8
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

### Query: `Tank Interface`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` | module `Mathlib.Tactic.Widget.LibraryRewrite` | package Mathlib | The structure with all data necessary for rendering a rewrite suggestion

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `Polarization State`
- `inner_map_polarization` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | A complex polarization identity, with a linear map.
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Polarization of an Associated Quadratic Map.** The polar bilinear form of the quadratic map induced by a bilinear map $B$ is equal to the sum of $B$ and its adjoint (the flipped bilinear map). That is, if $Q(x) = B(...
- `inner_map_polarization'` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | **Polarization Identity for Linear Operators on Complex Inner Product Spaces.** For any linear operator $T$ on a complex inner product space $V$ and any vectors $x, y \in V$, the inner product $\langle Tx, y \rangle$...

### Query: `Diagram Plane`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.

### Query: `Tank Wall Reflection Setup`
- `LinearMap.IsReflective.reflective_reflection` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | **Reflectivity of Reflected Vectors.** Let $B$ be a symmetric bilinear form on a module $M$. If $x$ and $y$ are reflective vectors with respect to $B$, then the reflection of $y$ across the hyperplane orthogonal to $x...
- `CoxeterSystem.IsReflection.not_isRightInversion_mul_left_iff` | module `Mathlib.GroupTheory.Coxeter.Inversion` | package Mathlib | **Right Inversion Property of Reflections.** For any element $w$ in a Coxeter system and any reflection $t$, $t$ is a right inversion of $w$ if and only if $t$ is not a right inversion of $wt$.
- `Module.reflection_apply` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | **Reflection Formula.** For a module $M$ over a ring $R$, let $x \in M$ and $f \in M^*$ be a linear form such that $f(x) = 2$. The reflection associated with $x$ and $f$ maps any element $y \in M$ to $y - f(y) \cdot x$.

### Query: `Has Tank Normal Angle Readouts`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `CategoryTheory.NormalMonoCategory.hasEqualizers` | module `Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers` | package Mathlib | A `NormalMonoCategory` category with finite products and kernels has all equalizers.
- `Orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | A side of a right-angled triangle divided by the tangent of the opposite angle equals the adjacent side.

### Query: `Satisfies Snell Law At Water Surface`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...
- `MSSMACC.AnomalyFreePerp.InQuadSolProp` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols` | package PhysLean | A condition which is satisfied if the plane spanned by the solutions `R`, `Y₃` and `B₃` lies entirely in the quadratic surface.

### Query: `Satisfies Brewster Polarization Law`
- `LinearMap.polar_eq_iInter` | module `Mathlib.Analysis.LocallyConvex.Polar` | package Mathlib | **Polar as an Intersection.** Given a bilinear form $B$ on $E \times F$, the polar of a subset $s \subseteq E$ is equal to the intersection over all $x \in s$ of the sets $\{y \in F \mid \|B(x, y)\| \leq 1\}$.
- `inner_map_polarization'` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | **Polarization Identity for Linear Operators on Complex Inner Product Spaces.** For any linear operator $T$ on a complex inner product space $V$ and any vectors $x, y \in V$, the inner product $\langle Tx, y \rangle$...
- `LinearMap.mem_polar_singleton` | module `Mathlib.Analysis.LocallyConvex.Polar` | package Mathlib | **Membership in the Polar of a Singleton.** Let $B$ be a bilinear map from $E \times F$ to a normed ring. For any $x \in E$ and $y \in F$, $y$ belongs to the polar of the singleton set $\{x\}$ if and only if the norm...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `inner_map_polarization` (Mathlib)
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` (Mathlib)
- `inner_map_polarization'` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `LinearMap.IsReflective.reflective_reflection` (Mathlib)
- `CoxeterSystem.IsReflection.not_isRightInversion_mul_left_iff` (Mathlib)
- `Module.reflection_apply` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `CategoryTheory.NormalMonoCategory.hasEqualizers` (Mathlib)
- `Orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)
- `MSSMACC.AnomalyFreePerp.InQuadSolProp` (PhysLean)
- `LinearMap.polar_eq_iInter` (Mathlib)
- `inner_map_polarization'` (Mathlib)
- `LinearMap.mem_polar_singleton` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0103.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.DiagramPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.HasTankNormalAngleReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.IsClosestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.MatchesTankWallProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.PolarizationState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.SatisfiesBrewsterPolarizationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.SatisfiesSnellLawAtWaterSurface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.SatisfiesTankFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.SatisfiesTankOpticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.TankInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0103.TankWallReflectionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

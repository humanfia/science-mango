# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0037.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0037.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:42a580b75e42b92e7c73bc65e6c79cac15bbd22b6d787a02abbf943bf74e73d9
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

### Query: `Polarization State`
- `inner_map_polarization` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | A complex polarization identity, with a linear map.
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Polarization of an Associated Quadratic Map.** The polar bilinear form of the quadratic map induced by a bilinear map $B$ is equal to the sum of $B$ and its adjoint (the flipped bilinear map). That is, if $Q(x) = B(...
- `inner_map_polarization'` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | **Polarization Identity for Linear Operators on Complex Inner Product Spaces.** For any linear operator $T$ on a complex inner product space $V$ and any vectors $x, y \in V$, the inner product $\langle Tx, y \rangle$...

### Query: `Pool Reflection Setup`
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `ComplexShape.Embedding.instIsRelIffOp` | module `Mathlib.Algebra.Homology.Embedding.Basic` | package Mathlib | **Reflectivity of Opposite Embeddings.** If an embedding of complex shapes is reflective, meaning it preserves the relation between indices in both directions, then its opposite embedding is also reflective.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `Has Normal Angle Readouts`
- `InnerProductGeometry.angle_normalize_left` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic` | package Mathlib | The angle between a normalized vector and another vector is equal to the angle between the original vectors.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `CategoryTheory.NormalMonoCategory.hasEqualizers` | module `Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Equalizers` | package Mathlib | A `NormalMonoCategory` category with finite products and kernels has all equalizers.

### Query: `Satisfies Snell Law`
- `Sat.Valuation.satisfies_fmla` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation. A formula is satisfied if all clauses in it are satisfied.
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...

### Query: `Pool Figure Readouts`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_le_of_coeff_ne_zero` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Order Bound for Hahn Series.** For any Hahn series $x$ over a linearly ordered set $\Gamma$, if the coefficient of $x$ at an index $g \in \Gamma$ is non-zero, then the order of $x$ is less than or equal to $g$.
- `HahnSeries.order_lt_iff_exists` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Characterization of the Order of a Hahn Series.** For a non-zero Hahn series $x$ and an element $i$ in the index set $\Gamma$, the order of $x$ is strictly less than $i$ if and only if there exists some $j < i$ such...

### Query: `Pool Optics Laws`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_le_of_coeff_ne_zero` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Order Bound for Hahn Series.** For any Hahn series $x$ over a linearly ordered set $\Gamma$, if the coefficient of $x$ at an index $g \in \Gamma$ is non-zero, then the order of $x$ is less than or equal to $g$.
- `HahnSeries.order_lt_iff_exists` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Characterization of the Order of a Hahn Series.** For a non-zero Hahn series $x$ and an element $i$ in the index set $\Gamma$, the order of $x$ is strictly less than $i$ if and only if there exists some $j < i$ such...

### Query: `Answer Choice`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `abs_choice` | module `Mathlib.Algebra.Order.Group.Unbundled.Abs` | package Mathlib | **Absolute Value Choice.** In a linearly ordered group, the absolute value of an element $x$ is equal to either $x$ or its inverse $x^{-1}$.
- `max_choice` | module `Mathlib.Order.MinMax` | package Mathlib | **Maximum Choice.** For any two elements $a$ and $b$ in a linearly ordered set, their maximum is equal to either $a$ or $b$.

### Query: `answer Angle Degrees`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_two_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **The Angle of $2\pi$.** The real number $2\pi$, when considered as an angle, is equal to the zero angle.
- `EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | If the angle ∠ABC at a point is π, the angle ∠BCA is 0.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `inner_map_polarization` (Mathlib)
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` (Mathlib)
- `inner_map_polarization'` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `ComplexShape.Embedding.instIsRelIffOp` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `InnerProductGeometry.angle_normalize_left` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `CategoryTheory.NormalMonoCategory.hasEqualizers` (Mathlib)
- `Sat.Valuation.satisfies_fmla` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_le_of_coeff_ne_zero` (Mathlib)
- `HahnSeries.order_lt_iff_exists` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_le_of_coeff_ne_zero` (Mathlib)
- `HahnSeries.order_lt_iff_exists` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `abs_choice` (Mathlib)
- `max_choice` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_two_pi` (Mathlib)
- `EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_right` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0037.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.HasNormalAngleReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.MatchesAnswerToNearestTenthDegree`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.PolarizationState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.PoolFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.PoolOpticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.PoolReflectionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0037.SatisfiesSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

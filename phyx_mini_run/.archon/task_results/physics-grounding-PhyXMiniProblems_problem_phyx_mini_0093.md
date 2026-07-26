# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0093.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0093.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:3f80181ef05c74a1565d49f9c427c4692cba06239862334935d88e9708f29226
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `optical Intensity Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.Θ𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to temperature.

### Query: `Optical Intensity`
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `PosNum.ofZNum'` | module `Mathlib.Data.Num.Basic` | package Mathlib | Converts a `ZNum` to `Option PosNum`, where it is `some` if the `ZNum` was positive and `none` otherwise.
- `Order.isIntent_iff` | module `Mathlib.Order.Concept` | package Mathlib | **Characterization of Intents.** For a binary relation $r$, a subset $t$ of the codomain is an intent if and only if it is equal to the upper polar of its lower polar with respect to $r$.

### Query: `Polarization State`
- `inner_map_polarization` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | A complex polarization identity, with a linear map.
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Polarization of an Associated Quadratic Map.** The polar bilinear form of the quadratic map induced by a bilinear map $B$ is equal to the sum of $B$ and its adjoint (the flipped bilinear map). That is, if $Q(x) = B(...
- `inner_map_polarization'` | module `Mathlib.Analysis.InnerProductSpace.LinearMap` | package Mathlib | **Polarization Identity for Linear Operators on Complex Inner Product Spaces.** For any linear operator $T$ on a complex inner product space $V$ and any vectors $x, y \in V$, the inner product $\langle Tx, y \rangle$...

### Query: `Light Beam`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `LightCondensed` | module `Mathlib.Condensed.Light.Basic` | package Mathlib | `LightCondensed.{u} C` is the category of light condensed objects in a category `C`, which are defined as sheaves on `LightProfinite.{u}` with respect to the coherent Grothendieck topology.

### Query: `Ideal Linear Polarizer`
- `Ideal` | module `Mathlib.RingTheory.Ideal.Defs` | package Mathlib | A (left) ideal in a semiring `R` is an additive submonoid `s` such that `a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.
- `Ideal.isLinearTopology` | module `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology` | package Mathlib | **The Adic Topology is a Linear Topology.** For any ideal $I$ of a ring $R$, the $I$-adic topology on $R$ is a linear topology.
- `QuadraticMap.polar_smul_left` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Linearity of the Polar Form in the First Argument.** For a quadratic map $Q$ on a module $M$ over a commutative ring $R$, the polar form of $Q$ is linear with respect to scalar multiplication in its first argument....

### Query: `Passes Through Ideal Linear Polarizer`
- `Mathlib.TacticAnalysis.runPasses` | module `Mathlib.Tactic.TacticAnalysis` | package Mathlib | Run the tactic analysis passes from `configs` on the tactic sequences in `stx`, using `trees` to get the infotrees.
- `Ideal` | module `Mathlib.RingTheory.Ideal.Defs` | package Mathlib | A (left) ideal in a semiring `R` is an additive submonoid `s` such that `a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.
- `PureU1.Odd.lineInCubicPerm_last_perm` | module `Physlib.QFT.QED.AnomalyCancellation.Odd.LineInCubic` | package PhysLean | **Line in Cubic Permutation Implies Line in Plane Condition.** For any linear solution $S$ of the system $PureU1(2n + 3)$, if $S$ satisfies the line in cubic permutation property, then it necessarily satisfies the lin...

### Query: `Three Polarizer Setup`
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `upperPolar_lowerPolar_upperPolar` | module `Mathlib.Order.Concept` | package Mathlib | **Triple Polar Identity.** For any binary relation $r$ and any set $s$, the upper polar of the lower polar of the upper polar of $s$ is equal to the upper polar of $s$.
- `lowerPolar_upperPolar_lowerPolar` | module `Mathlib.Order.Concept` | package Mathlib | **Triple Lower Polar Identity.** For any relation $r$ and any set $t$, the lower polar of the upper polar of the lower polar of $t$ is equal to the lower polar of $t$.

### Query: `Three Polarizer Figure Readouts`
- `pow_three` | module `Mathlib.Algebra.Group.Defs` | package Mathlib | Cube of an Element. For any element $a$ in a monoid, $a^3$ is equal to $a * (a * a)$.
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `QuadraticMap.polarSym2_sym2Mk` | module `Mathlib.LinearAlgebra.QuadraticForm.Basic` | package Mathlib | **Polarization of a Quadratic Map on Symmetric Pairs.** For any function $f: M \to N$ and any two elements $x, y \in M$, the evaluation of the symmetric polarization of $f$ at the unordered pair $\{x, y\}$ is equal to...

### Query: `Three Polarizer Optics Laws`
- `pow_three` | module `Mathlib.Algebra.Group.Defs` | package Mathlib | Cube of an Element. For any element $a$ in a monoid, $a^3$ is equal to $a * (a * a)$.
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `PolynomialLaw.comp_assoc` | module `Mathlib.RingTheory.PolynomialLaw.Basic` | package Mathlib | **Associativity of Composition for Polynomial Laws.** For any three polynomial laws $f$, $g$, and $h$ between appropriate modules over a commutative semiring, the composition of these laws is associative: $h \circ (g...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.Θ𝓭` (PhysLean)
- `intervalIntegral` (Mathlib)
- `PosNum.ofZNum'` (Mathlib)
- `Order.isIntent_iff` (Mathlib)
- `inner_map_polarization` (Mathlib)
- `LinearMap.BilinMap.polarBilin_toQuadraticMap` (Mathlib)
- `inner_map_polarization'` (Mathlib)
- `LightProfinite` (Mathlib)
- `LightDiagram'` (Mathlib)
- `LightCondensed` (Mathlib)
- `Ideal` (Mathlib)
- `Ideal.isLinearTopology` (Mathlib)
- `QuadraticMap.polar_smul_left` (Mathlib)
- `Mathlib.TacticAnalysis.runPasses` (Mathlib)
- `Ideal` (Mathlib)
- `PureU1.Odd.lineInCubicPerm_last_perm` (PhysLean)
- `EuclideanGeometry.oangle` (Mathlib)
- `upperPolar_lowerPolar_upperPolar` (Mathlib)
- `lowerPolar_upperPolar_lowerPolar` (Mathlib)
- `pow_three` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `QuadraticMap.polarSym2_sym2Mk` (Mathlib)
- `pow_three` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `PolynomialLaw.comp_assoc` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0093.IdealLinearPolarizer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.LightBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.OpticalIntensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.PassesThroughIdealLinearPolarizer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.PolarizationState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.ThreePolarizerFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.ThreePolarizerOpticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0093.ThreePolarizerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

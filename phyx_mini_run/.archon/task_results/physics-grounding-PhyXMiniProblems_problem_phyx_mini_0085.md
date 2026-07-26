# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0085.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0085.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8f6796f7b6804c0c4cd271bc09c89305ff094f83a08cf8ff15fabf446e4a8b48
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `Dim Time`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.T𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the time dimension.** The mass dimension component of the time dimension $T_d$ is equal to zero.

### Query: `Dim Speed`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `millimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `picosecond Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `TimeUnit.picoseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of picoseconds (10⁻¹² of a second).

### Query: `Plastic Layer`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order_C` | module `Mathlib.RingTheory.HahnSeries.Multiplication` | package Mathlib | **Order of a Constant Hahn Series.** For any element $r$ in a ring $R$, the order of the constant Hahn series $C(r)$ is equal to $0$.

### Query: `Laser Pistol`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `εNFA.evalFrom` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element of `S`.

### Query: `Array Side`
- `EuclideanGeometry.side_side_side` | module `Mathlib.Geometry.Euclidean.Congruence` | package Mathlib | **Side–Side–Side (SSS) congruence** If all three corresponding sides of two triangles are equal, then the triangles are congruent. This holds even if the triangles are degenerate.
- `similar_of_side_side` | module `Mathlib.Topology.MetricSpace.Similarity` | package Mathlib | **Alias** of `similar_of_dist_mul_eq_dist_mul_eq`. --- If two triangles have two pairs of proportional adjacent sides, then the triangles are similar.
- `AffineSubspace.WSameSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are weakly on the same side of `s`.

### Query: `Pistol3 Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `WeierstrassCurve.baseChange_Ψ₃` | module `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` | package Mathlib | **Base Change of the Division Polynomial $\Psi_3$.** For a Weierstrass curve $W$ defined over a ring $A$ and a ring homomorphism $f: A \to B$, the third division polynomial $\Psi_3$ of the base-changed curve $W_B$ is...
- `WeierstrassCurve.ΨSq_three` | module `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` | package Mathlib | **Square of the Third Division Polynomial.** For a Weierstrass curve $W$, the squared division polynomial $\Psi^2$ at $n = 3$ is equal to the square of the third division polynomial $\Psi_3$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.T𝓭_mass` (PhysLean)
- `DimSpeed` (PhysLean)
- `dimH` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `TimeUnit.picoseconds` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order_C` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `εNFA.evalFrom` (Mathlib)
- `EuclideanGeometry.side_side_side` (Mathlib)
- `similar_of_side_side` (Mathlib)
- `AffineSubspace.WSameSide` (Mathlib)
- `segment` (Mathlib)
- `WeierstrassCurve.baseChange_Ψ₃` (Mathlib)
- `WeierstrassCurve.ΨSq_three` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0085.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.ArcadeArrayFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.ArcadeArraySetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.ArraySide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.DimSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.HasAllowedThickness`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.LaserPistol`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.Pistol3Burst`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.Pistol3Segment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.Pistol3TransitLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0085.PlasticLayer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0071.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0071.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8191e9a29b1c88c075d2720934ed3873580e721e1dea3f91fc554fefe061db84
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

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Tank Wall`
- `instTopologicalSpaceTangentSpace` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | **Topological Structure of the Tangent Space.** For a manifold $M$ modeled on a space $H$ with model vector space $E$ over a nontrivially normed field $\mathbb{k}$, the tangent space at any point $x \in M$ is equipped...
- `instModuleTangentSpace` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | **Module Structure on the Tangent Space.** For a manifold $M$ modeled on a space $H$ with an underlying model vector space $E$ over a nontrivially normed field $\mathbb{k}$, the tangent space at any point $x \in M$ is...
- `UpperHalfPlane.instT4Space` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Topology` | package Mathlib | **The Upper Half-Plane is a $T_4$ Space.** The upper half-plane $\mathbb{H}$ satisfies the $T_4$ separation axiom; that is, it is both a $T_1$ space and a normal space.

### Query: `Tank Contents`
- `MvPFunctor.appendContents` | module `Mathlib.Data.PFunctor.Multivariate.Basic` | package Mathlib | append arrows of a polynomial functor application
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MvPFunctor.M.corecContents` | module `Mathlib.Data.PFunctor.Multivariate.M` | package Mathlib | Using corecursion, construct the contents of an M-type

### Query: `source Question Contents`
- `MvPFunctor.appendContents` | module `Mathlib.Data.PFunctor.Multivariate.Basic` | package Mathlib | append arrows of a polynomial functor application
- `MvPFunctor.M.corecContents` | module `Mathlib.Data.PFunctor.Multivariate.M` | package Mathlib | Using corecursion, construct the contents of an M-type
- `Equidecomp.source_restr` | module `Mathlib.Algebra.Group.Action.Equidecomp` | package Mathlib | **Source of a Restricted Equidecomposition.** Given an equidecomposition $f$ and a subset $A$ of its source, the source of the restriction of $f$ to $A$ is exactly $A$.

### Query: `pictured Scenario Contents`
- `MvPFunctor.appendContents` | module `Mathlib.Data.PFunctor.Multivariate.Basic` | package Mathlib | append arrows of a polynomial functor application
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MvPFunctor.M.corecContents` | module `Mathlib.Data.PFunctor.Multivariate.M` | package Mathlib | Using corecursion, construct the contents of an M-type

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Depth Mark`
- `WType.depth` | module `Mathlib.Data.W.Basic` | package Mathlib | The depth of a finitely branching tree.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `WType.depth_pos` | module `Mathlib.Data.W.Basic` | package Mathlib | **Positivity of Tree Depth.** For any well-founded tree $t$ in a $W$-type, the depth of $t$ is strictly greater than zero.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `instTopologicalSpaceTangentSpace` (Mathlib)
- `instModuleTangentSpace` (Mathlib)
- `UpperHalfPlane.instT4Space` (Mathlib)
- `MvPFunctor.appendContents` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MvPFunctor.M.corecContents` (Mathlib)
- `MvPFunctor.appendContents` (Mathlib)
- `MvPFunctor.M.corecContents` (Mathlib)
- `Equidecomp.source_restr` (Mathlib)
- `MvPFunctor.appendContents` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MvPFunctor.M.corecContents` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `WType.depth` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `WType.depth_pos` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0071.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.DepthMark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.IsCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.IsNearestDisplayedMark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.MatchesTankProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.ModelsOrdinaryWaterAndAir`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.ObservationPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.SatisfiesGrazingWaterAirRefraction`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.SatisfiesLimitingSightlineGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.TankContents`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.TankDepthScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.TankViewingSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0071.TankWall`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

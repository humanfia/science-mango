# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0062.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0062.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ec22de99e6c78c6061c0a2860d852e2a31345e9dc29d6b4b1ba1f5cabc3971bf
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Mirror Shape`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `CategoryTheory.OrthogonalReflection.D₂.multispanShape` | module `Mathlib.CategoryTheory.Presentable.OrthogonalReflection` | package Mathlib | The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W Z` with a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.
- `ComplexShape.instHasNoLoopSymm` | module `Mathlib.Algebra.Homology.HasNoLoop` | package Mathlib | **Irreflexivity of the Symmetric Complex Shape.** If a complex shape is irreflexive, then its symmetric (reverse) complex shape is also irreflexive.

### Query: `Mirror Rotation`
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `rotationOf_rotation` | module `Mathlib.Analysis.Complex.Isometry` | package Mathlib | **Rotation of a Circle Rotation.** For any element $a$ of the unit circle, the rotation associated with the isometric automorphism defined by $a$ is equal to $a$ itself.

### Query: `Laser Aim`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `getGoalLocations` | module `Mathlib.Tactic.Widget.SelectPanelUtils` | package Mathlib | Given a `Array GoalsLocation` return the array of `SubExpr.Pos` for all locations in the targets of the relevant goals.

### Query: `Wall Placement`
- `DiscreteTiling.PlacedTile.mem_coe` | module `Mathlib.Combinatorics.Tiling.Tile` | package Mathlib | **Membership in a Placed Tile.** An element $x$ belongs to the set representation of a placed tile $pt$ if and only if $x$ is an element of $pt$.
- `DiscreteTiling.PlacedTile.instMembership` | module `Mathlib.Combinatorics.Tiling.Tile` | package Mathlib | **Membership for Placed Tiles.** An element $x \in X$ is a member of a placed tile $p$ if $x$ is contained in the set of points in $X$ that constitutes the placed tile.
- `Alignment` | module `Mathlib.Util.FormatTable` | package Mathlib | Possible alignment modes for each table item: left-aligned, right-aligned and centered.

### Query: `Sweep Endpoint`
- `SimpleGraph.Walk.endpoint_notMem_support_takeUntil` | module `Mathlib.Combinatorics.SimpleGraph.Paths` | package Mathlib | Taking a strict initial segment of a path removes the end vertex from the support.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `AddCircle.EndpointIdent` | module `Mathlib.Topology.Instances.AddCircle.Defs` | package Mathlib | The relation identifying the endpoints of `Icc a (a + p)`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Polynomial.mirror` (Mathlib)
- `CategoryTheory.OrthogonalReflection.D₂.multispanShape` (Mathlib)
- `ComplexShape.instHasNoLoopSymm` (Mathlib)
- `Orientation.rotation` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `rotationOf_rotation` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `getGoalLocations` (Mathlib)
- `DiscreteTiling.PlacedTile.mem_coe` (Mathlib)
- `DiscreteTiling.PlacedTile.instMembership` (Mathlib)
- `Alignment` (Mathlib)
- `SimpleGraph.Walk.endpoint_notMem_support_takeUntil` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `AddCircle.EndpointIdent` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0062.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.HasDepictedOpticalLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.HasPhysicalDimensions`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.IsNearestDisplayedStreakLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.LaserAim`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.MirrorRotation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.MirrorShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.RotatingHexagonalMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.SatisfiesLawOfSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.SatisfiesRegularHexagonTransitionGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.SatisfiesWallProjectionGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.SweepEndpoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0062.WallPlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

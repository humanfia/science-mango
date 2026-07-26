# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0735.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0735.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:6858cd8151c6da01d96073ff51674fc186286210f4e135bea6dc96e10f51e937
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Fault Plane Vector`
- `PureU1.VectorLikeEvenPlane.P_evenFst` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Projection onto the First Basis Element of an Even Plane.** For any charge distribution $f$ indexed by $\{0, \dots, n\}$ and any index $j$, the linear functional $P$ evaluated at the $j$-th basis vector of the even...
- `vectorSpan` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The submodule spanning the differences of a (possibly empty) set of points.
- `PureU1.VectorLikeEvenPlane.basis!AsCharges` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | The second part of the basis as charges.

### Query: `Displacement Vector`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `AffineMap.lineMap_vsub_left` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | **Vector Displacement from the Start of an Affine Line Map.** For any two points $p_0, p_1$ in an affine space and a scalar $c$, the displacement vector from $p_0$ to the point $c$ along the line through $p_0$ and $p_...
- `RigidBodyMotion.displacement_apply` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The `k`-th coordinate of the rigid displacement applied to `y`.

### Query: `displacement Readout`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.displacement_apply` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The `k`-th coordinate of the rigid displacement applied to `y`.

### Query: `displacement In Meters`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.

### Query: `displacement Magnitude Readout`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBodyMotion.displacement_apply` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The `k`-th coordinate of the rigid displacement applied to `y`.

### Query: `displacement Magnitude In Meters`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.

### Query: `Fault Point`
- `CategoryTheory.GrothendieckTopology.Point` | module `Mathlib.CategoryTheory.Sites.Point.Basic` | package Mathlib | Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)` consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements` is initially small (which allows defining the fiber...
- `ClusterPt` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`. Also known as an accumulation point or a limit point, but beware that terminology varies. This is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`, which is ca...
- `MapClusterPt` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point of `map u F`.

### Query: `Fault Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `affineSegment` | module `Mathlib.Analysis.Convex.Between` | package Mathlib | The segment of points weakly between `x` and `y`. When convexity is refactored to support abstract affine combination spaces, this will no longer need to be a separate definition from `segment`. However, lemmas involv...
- `openSegment_same` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Open Segment of a Point with Itself.** For any element $x$ in a module $E$ over a densely ordered semiring $\mathbf{k}$, the open segment between $x$ and itself is the singleton set $\{x\}$.

### Query: `segment Start`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `Path.cast_segment` | module `Mathlib.Analysis.Convex.PathConnected` | package Mathlib | **Casting a Linear Path Segment.** Given a linear path segment from $a$ to $b$, if $c = a$ and $d = b$, then casting the path to have start point $c$ and end point $d$ results in the linear path segment from $c$ to $d$.
- `image_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Image of a Line Segment under an Affine Map.** For any affine map $f$ and any two points $a$ and $b$ in its domain, the image of the line segment connecting $a$ and $b$ is equal to the line segment connecting the im...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `PureU1.VectorLikeEvenPlane.P_evenFst` (PhysLean)
- `vectorSpan` (Mathlib)
- `PureU1.VectorLikeEvenPlane.basis!AsCharges` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `AffineMap.lineMap_vsub_left` (Mathlib)
- `RigidBodyMotion.displacement_apply` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.displacement_apply` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `JoinedIn` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBodyMotion.displacement_apply` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `JoinedIn` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `CategoryTheory.GrothendieckTopology.Point` (Mathlib)
- `ClusterPt` (Mathlib)
- `MapClusterPt` (Mathlib)
- `segment` (Mathlib)
- `affineSegment` (Mathlib)
- `openSegment_same` (Mathlib)
- `segment` (Mathlib)
- `Path.cast_segment` (Mathlib)
- `image_segment` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0735.DisplacementVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.FaultComponentLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.FaultPlaneFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.FaultPlaneVector`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.FaultPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.FaultSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.SegmentRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0735.SegmentStyle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

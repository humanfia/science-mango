# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0025.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0025.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Floor Plane`
- `Int.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`.
- `Int.floor_int` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | **Floor of an Integer.** The floor function restricted to the integers is the identity function; that is, for any integer $n$, $\lfloor n \rfloor = n$.
- `Nat.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`.

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `Dim Time`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `dim` | module `Physlib.Units.Basic` | package PhysLean | **Alias** of `HasDim.d`. --- The dimension associated with a type `M`.
- `Dimension.T𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the time dimension.** The mass dimension component of the time dimension $T_d$ is equal to zero.

### Query: `Dim Angular Speed`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `DimSpeed.oneKnot` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 knot, aka, one nautical mile per hour.

### Query: `Dim Linear Speed`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Floor Point`
- `Int.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`.
- `Int.floor_int` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | **Floor of an Integer.** The floor function restricted to the integers is the identity function; that is, for any integer $n$, $\lfloor n \rfloor = n$.
- `Pi.floorDiv_def` | module `Mathlib.Algebra.Order.Floor.Div` | package Mathlib | **Pointwise Floor Division.** For a family of elements $f$ in a product type and a scalar $a$, the floor division $f \lfloor/\rfloor a$ is defined pointwise; that is, for each index $i$, the $i$-th component of the re...

### Query: `Beam Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.

### Query: `Wall Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...
- `ReaderT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Continuation Labels to the Reader Monad Transformer.** Given a continuation label that maps values of type $\alpha$ to computations in a monad $m$ returning type $\beta$, we can construct a corresponding lab...

### Query: `Directed Beam`
- `DirectedOn` | module `Mathlib.Order.Directed` | package Mathlib | A subset of `α` is directed if there is an element of the set `≼`-above any pair of elements in the set.
- `DirectedOn.snd` | module `Mathlib.Order.Directed` | package Mathlib | **Directedness of the Second Projection.** If a set of pairs $d \subseteq \alpha \times \beta$ is directed with respect to the product relation (where $(a_1, b_1) \le (a_2, b_2)$ if and only if $a_1 \le_1 a_2$ and $b_...
- `Directed` | module `Mathlib.Order.Directed` | package Mathlib | A family of elements of `α` is directed (with respect to a relation `≼` on `α`) if there is a member of the family `≼`-above any pair in the family.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Int.floor` (Mathlib)
- `Int.floor_int` (Mathlib)
- `Nat.floor` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `dimH` (Mathlib)
- `dim` (PhysLean)
- `Dimension.T𝓭_mass` (PhysLean)
- `DimSpeed` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `DimSpeed.oneKnot` (PhysLean)
- `DimSpeed` (PhysLean)
- `dimH` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `Int.floor` (Mathlib)
- `Int.floor_int` (Mathlib)
- `Pi.floorDiv_def` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Space.toDirection` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `StateT.mkLabel` (Mathlib)
- `ReaderT.mkLabel` (Mathlib)
- `DirectedOn` (Mathlib)
- `DirectedOn.snd` (Mathlib)
- `Directed` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0025.BeamDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.DimAngularSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.DimLinearSpeed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.DimTime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.DirectedBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.FloorPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.FloorPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.InClosedTimeInterval`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.IsEastWallSweepFromOToCorner`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.IsMaximumSpotSpeedOn`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.IsMinimumSpotSpeedOn`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.MatchesRotatingMirrorFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.MatchesSquareRoomFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.PointOnBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.RotatingMirrorExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.RotatingMirrorOpticsLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.SquareRoomFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0025.WallLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

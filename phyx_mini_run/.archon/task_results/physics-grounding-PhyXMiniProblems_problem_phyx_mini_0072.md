# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0072.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0072.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:71621529ffca8f4b6fef363e0b23faf7dc00afa14ad63fa6f120bb36b18c7ca6
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

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Container Side`
- `AffineSubspace.WOppSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are weakly on opposite sides of `s`.
- `AffineSubspace.WSameSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are weakly on the same side of `s`.
- `AffineSubspace.SSameSide.right_notMem` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | **Strictly on the Same Side Implies Non-Containment.** If two points $x$ and $y$ lie strictly on the same side of an affine subspace $s$, then $y$ is not contained in $s$.

### Query: `Boundary Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Module.Basis.orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | The orientation given by a basis.

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Rectangular Water Box Setup`
- `BoxIntegral.Box` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Represents the product of half-open intervals `(lower i, upper i]`.
- `BoxIntegral.Box.mk'` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Make a `WithBot (Box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`, then the result is `⟨l, u, _⟩ : Box ι`, otherwise it is `⊥`. In any case, the result interpreted as a set in `ι → ℝ` is the se...
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.

### Query: `Laser Ray Path`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `Module.Ray.map_apply` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | **Mapping of Rays under Linear Equivalence.** For any linear equivalence $e$ between two modules $M$ and $N$ over a strictly ordered semiring, the induced map on rays sends the ray generated by a nonzero vector $v$ in...

### Query: `Has Depicted Rectangular Layout`
- `HasProd` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasProd f a L` means that the (potentially infinite) product of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finit...
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Help function for displaying two string diagrams in an equality.
- `Mathlib.Tactic.Widget.commutativeSquarePresenter` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Presenter for a commutative square

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
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `AffineSubspace.WOppSide` (Mathlib)
- `AffineSubspace.WSameSide` (Mathlib)
- `AffineSubspace.SSameSide.right_notMem` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Module.Basis.orientation` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `BoxIntegral.Box` (Mathlib)
- `BoxIntegral.Box.mk'` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `Module.Ray.map_apply` (Mathlib)
- `HasProd` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` (Mathlib)
- `Mathlib.Tactic.Widget.commutativeSquarePresenter` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0072.AdmissibleEntryDisplacementInCentimeters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.BoundaryOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.ContainerSide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.EmergesIntoAirThroughSideB`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.FollowsDepictedSideRoute`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.HasDepictedRectangularLayout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.HasPhysicalRayParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.LaserRayPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.MatchesEntryDisplacementChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.RectangularWaterBoxSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.SatisfiesPerpendicularSideGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.SatisfiesSnellLawAtSideA`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.SatisfiesSourceToEntryGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0072.SatisfiesWaterAirCriticalAngleLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

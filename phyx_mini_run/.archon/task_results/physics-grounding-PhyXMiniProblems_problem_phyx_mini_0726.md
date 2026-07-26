# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0726.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0726.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:31885d8b868db9b6caabff31538917f7ccb7d30a19e3d9e7ad623f6c985ec637
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

### Query: `length In Kilometers`
- `LengthUnit.kilometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of kilometers (10³ meters).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length In Feet`
- `LengthUnit.feet` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of feet (0.3048 meters)
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `DimArea.acre_eq_mul_squareFeet` | module `Physlib.Units.WithDim.Area` | package PhysLean | One acre is exactly `43560` square feet.

### Query: `Diagram Plane`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Figure Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `segment_eq_image'` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Segment as an Image.** For any two points $x$ and $y$ in a vector space $E$ over a scalar field $\mathbb{k}$, the closed segment $[x, y]$ is equal to the image of the unit interval $[0, 1] \subseteq \mathbb{k}$ unde...
- `image_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Image of a Line Segment under an Affine Map.** For any affine map $f$ and any two points $a$ and $b$ in its domain, the image of the line segment connecting $a$ and $b$ is equal to the line segment connecting the im...

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
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
- `LengthUnit.kilometers` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.feet` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `DimArea.acre_eq_mul_squareFeet` (PhysLean)
- `Complex.slitPlane` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `segment` (Mathlib)
- `segment_eq_image'` (Mathlib)
- `image_segment` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0726.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.DiagramPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.DistanceSource`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.EarthHorizonSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.EarthModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.FigureLengthLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.FigureRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.FigureSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.HasPhysicalLengths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.HasStatedObservationData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.IsClosestDisplayedRadius`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.ObeysSphericalEarthHorizonLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.ObserverSupport`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.SightTarget`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0726.VisibilityStatus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

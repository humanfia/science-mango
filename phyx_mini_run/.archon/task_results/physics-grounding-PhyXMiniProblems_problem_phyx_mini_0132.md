# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0132.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0132.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e60400e50b8ac967d01e57783d64b99f52de9bcf4958bdfde1a2b1fca5b18c08
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

### Query: `Radio Telescope Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.CrossRef.Database.label` | module `Mathlib.Tactic.CrossRefAttribute` | package Mathlib | The display label used in docstring links and trace output.
- `SuperSymmetry.SU5.ChargeSpectrum.ofFieldLabel` | module `Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel` | package PhysLean | Given an `x : Charges`, the charges associated with a given `FieldLabel`.

### Query: `Star Label`
- `StarConvex` | module `Mathlib.Analysis.Convex.Star` | package Mathlib | Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is contained in `s`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Star` | module `Mathlib.Algebra.Notation.Defs` | package Mathlib | Notation typeclass (with no default notation!) for an algebraic structure with a star operation.

### Query: `Astronomical Source Kind`
- `LengthUnit.astronomicalUnits` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of an astronomical unit (149,597,870,700 meters).
- `stereographic_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the domain (source) of the stereographic projection associated with $v$ is the complement of the singleton set containing...
- `stereographic'_source` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Domain of the Stereographic Projection.** For an $(n+1)$-dimensional real inner product space $E$ and a point $v$ on the unit sphere in $E$, the domain (source) of the stereographic projection from the sphere with p...

### Query: `Aperture Shape`
- `CategoryTheory.Limits.WidePushoutShape` | module `Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks` | package Mathlib | A wide pushout shape for any type `J` can be written simply as `Option J`.
- `CategoryTheory.Limits.HasLimitsOfShape` | module `Mathlib.CategoryTheory.Limits.HasLimits` | package Mathlib | `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`.
- `ComplexShape` | module `Mathlib.Algebra.Homology.ComplexShape` | package Mathlib | A `c : ComplexShape ι` describes the shape of a chain complex, with chain groups indexed by `ι`. Typically `ι` will be `ℕ`, `ℤ`, or `Fin n`. There is a relation `Rel : ι → ι → Prop`, and we will only allow a non-zero...

### Query: `Reflector Geometry`
- `CategoryTheory.reflector` | module `Mathlib.CategoryTheory.Adjunction.Reflective` | package Mathlib | The reflector `C ⥤ D` when `R : D ⥤ C` is reflective.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.
- `EuclideanGeometry.angle_pointReflection_right` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | **Angle with a Point Reflected across the Vertex.** For any three points $p_1, p_2$, and $p_3$ in a Euclidean space, the angle $\angle p_1 p_2 p_3'$ formed by $p_1$, $p_2$, and the reflection $p_3'$ of $p_3$ across $p...

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
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.CrossRef.Database.label` (Mathlib)
- `SuperSymmetry.SU5.ChargeSpectrum.ofFieldLabel` (PhysLean)
- `StarConvex` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Star` (Mathlib)
- `LengthUnit.astronomicalUnits` (PhysLean)
- `stereographic_source` (Mathlib)
- `stereographic'_source` (Mathlib)
- `CategoryTheory.Limits.WidePushoutShape` (Mathlib)
- `CategoryTheory.Limits.HasLimitsOfShape` (Mathlib)
- `ComplexShape` (Mathlib)
- `CategoryTheory.reflector` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `EuclideanGeometry.angle_pointReflection_right` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0132.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.ApertureShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.AreciboResolutionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.AstronomicalSourceKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.IsUniqueMatchingAngularSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.MatchesDisplayedAngularSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.MatchesScenarioAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.RadioTelescopeLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.ReflectorGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.ResolutionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.SatisfiesCircularApertureRayleighCriterion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0132.StarLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

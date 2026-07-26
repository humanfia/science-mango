# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0249.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0249.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:dacbf83f156701a82bafaf46df1609780142d184ec57bbb5d7b74c158bba8a09
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

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

### Query: `length In Millimeters`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `Laser Kind`
- `Mathlib.Notation3.foldKind` | module `Mathlib.Util.Notation3` | package Mathlib | Keywording indicating whether to use a left- or right-fold.
- `Mathlib.Tactic.Widget.StringDiagram.Kind` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | The kind of the context.
- `Mathlib.Tactic.ITauto.AndKind` | module `Mathlib.Tactic.ITauto` | package Mathlib | Different propositional constructors that are variants of "and" for the purposes of the theorem prover.

### Query: `Slit Geometry`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `Complex.starConvex_ofReal_slitPlane` | module `Mathlib.Analysis.Complex.Convex` | package Mathlib | The slit plane is star-shaped at a positive real number.
- `Complex.mem_slitPlane_iff` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | **Membership in the Slit Plane.** A complex number $z$ belongs to the slit plane if and only if its real part is strictly positive or its imaginary part is non-zero.

### Query: `Optical Regime`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `linter.tacticAnalysis.regressions.omegaToLia` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Debug `lia` by identifying places where it does not yet supersede `omega`.
- `linter.tacticAnalysis.regressions.ringToGrind` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Debug `grind` by identifying places where it does not yet supersede `ring`.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `Mathlib.Notation3.foldKind` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.Kind` (Mathlib)
- `Mathlib.Tactic.ITauto.AndKind` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `Complex.starConvex_ofReal_slitPlane` (Mathlib)
- `Complex.mem_slitPlane_iff` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `linter.tacticAnalysis.regressions.omegaToLia` (Mathlib)
- `linter.tacticAnalysis.regressions.ringToGrind` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0249.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.ConnectsExperimentToScaledFamily`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.IsPositiveAcuteAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.IsUniqueMatchingDisplayedWidth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.LaserKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.MatchesDisplayedWidth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.MatchesProblemAndFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.OpticalRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.SatisfiesExactScreenRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.SatisfiesFraunhoferParaxialAsymptotics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.SingleSlitDiffractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0249.SlitGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0530.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0530.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7ed0f9b4f1c2f46a9a30ba3ae9085f0e3cdf62cf4fefa1731f8088b58dbe6f34
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

### Query: `Direction2 D`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `prevD` | module `Mathlib.Algebra.Homology.Homotopy` | package Mathlib | The composition `f j (c.prev j) ≫ D.d (c.prev j) j`.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Picometers`
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `direction Angle`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Orientation.oangle_add_right_smul_rotation_pi_div_two` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle` | package Mathlib | An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple of a rotation of another by `π / 2`.

### Query: `Interaction Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Photon Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Electron Label`
- `SuperSymmetry.SU5.ChargeSpectrum.ofFieldLabel` | module `Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel` | package PhysLean | Given an `x : Charges`, the charges associated with a given `FieldLabel`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.

### Query: `Figure Angle Label`
- `Real.Angle.sign` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the sign of the sine of the angle.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are equal.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `prevD` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.picometers` (PhysLean)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `Space.Direction` (PhysLean)
- `Orientation.oangle_add_right_smul_rotation_pi_div_two` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `SuperSymmetry.SU5.ChargeSpectrum.ofFieldLabel` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Real.Angle.sign` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0530.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.Direction2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.ElectronLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.FigureAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.HasPhysicalSequentialComptonParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.InteractionPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.MatchesElectronComptonWavelengthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.MatchesSequentialComptonFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.MatchesSequentialScatteringScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.PhotonLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.PhotonState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.RoundsToNearestHundredthPicometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.SatisfiesTwoStageComptonScatteringLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.SequentialComptonFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0530.SequentialComptonSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

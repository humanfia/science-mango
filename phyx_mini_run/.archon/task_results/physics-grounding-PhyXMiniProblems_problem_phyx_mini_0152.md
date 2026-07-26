# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0152.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0152.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f1e0b4294eeaf60654e5fc5975cb11782754a5d86748bc41c18a69389295285f
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

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `Cell State`
- `SSet.relativeCellComplex` | module `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` | package Mathlib | If `X` is a simplicial set, then the inclusion `(⊥ : SSet) ⟶ X` of the empty subcomplex of `X` is a relative cell complex with basic cells given by boundary inclusions `∂Δ[d] ⟶ Δ[d]`, one for each nondegenerate `d`-si...
- `Topology.RelCWComplex.closedCell` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1` whenever possible.
- `Topology.CWComplex.cell_def` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | **CW Complex as a Relative CW Complex.** Every CW complex $C$ in a topological space $X$ naturally inherits the structure of a relative CW complex $(C, \emptyset)$ over the empty set. Consequently, the indexing set fo...

### Query: `Figure Element`
- `commutatorElement` | module `Mathlib.Algebra.Group.Commutator` | package Mathlib | The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Top` | module `Mathlib.Order.Notation` | package Mathlib | Typeclass for the `⊤` (`\top`) notation

### Query: `Beam Leg`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Limits.Multicofork.ofSigmaCofork_ι_app_right'` | module `Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | package Mathlib | **Alias** of `CategoryTheory.Limits.Multicofork.ofSigmaCofork_π`.
- `CategoryTheory.Limits.Multicofork.ofSigmaCofork_ι_app_right` | module `Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | package Mathlib | **Alias** of `CategoryTheory.Limits.Multicofork.ofSigmaCofork_π`.

### Query: `Propagation Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Space.toDirection` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Direction of a `Space` value with respect to the origin.

### Query: `Gas Cell Interferometer`
- `Topology.RelCWComplex.closedCell` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1` whenever possible.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `Topology.RelCWComplex.openCell` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0 1` whenever possible.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `SSet.relativeCellComplex` (Mathlib)
- `Topology.RelCWComplex.closedCell` (Mathlib)
- `Topology.CWComplex.cell_def` (Mathlib)
- `commutatorElement` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Top` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Limits.Multicofork.ofSigmaCofork_ι_app_right'` (Mathlib)
- `CategoryTheory.Limits.Multicofork.ofSigmaCofork_ι_app_right` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Space.toDirection` (PhysLean)
- `Topology.RelCWComplex.closedCell` (Mathlib)
- `IdealGas` (PhysLean)
- `Topology.RelCWComplex.openCell` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0152.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.BeamLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.CellState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.FigureElement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.GasCellInterferometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.HasStatedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.HasVacuumReferenceIndex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.IsNearestMillionthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.MatchesSourceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.ObeysFringeCountingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.ObeysGasCellOpticalPathLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0152.PropagationDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0250.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0250.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b081e0a0161da05fcfa5352f760da1e2b1c092f97b1a15fa019393d4b138c4cd
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

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `Laser Kind`
- `Mathlib.Notation3.foldKind` | module `Mathlib.Util.Notation3` | package Mathlib | Keywording indicating whether to use a left- or right-fold.
- `Mathlib.Tactic.Widget.StringDiagram.Kind` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | The kind of the context.
- `Mathlib.Tactic.ITauto.AndKind` | module `Mathlib.Tactic.ITauto` | package Mathlib | Different propositional constructors that are variants of "and" for the purposes of the theorem prover.

### Query: `Cell State`
- `SSet.relativeCellComplex` | module `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` | package Mathlib | If `X` is a simplicial set, then the inclusion `(⊥ : SSet) ⟶ X` of the empty subcomplex of `X` is a relative cell complex with basic cells given by boundary inclusions `∂Δ[d] ⟶ Δ[d]`, one for each nondegenerate `d`-si...
- `Topology.RelCWComplex.closedCell` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1` whenever possible.
- `Topology.CWComplex.cell_def` | module `Mathlib.Topology.CWComplex.Classical.Basic` | package Mathlib | **CW Complex as a Relative CW Complex.** Every CW complex $C$ in a topological space $X$ naturally inherits the structure of a relative CW complex $(C, \emptyset)$ over the empty set. Consequently, the indexing set fo...

### Query: `Filling Protocol`
- `SSet.Quasicategory.hornFilling` | module `Mathlib.AlgebraicTopology.Quasicategory.Basic` | package Mathlib | **Horn Filling for Quasicategories.** In a quasicategory $S$, every inner horn has a filler. Specifically, for any $n \in \mathbb{N}$ and any $0 < i < n$, any morphism of simplicial sets $\sigma_0 : \Lambda^n_i \to S$...
- `SSet.KanComplex.hornFilling` | module `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex` | package Mathlib | A Kan complex `S` satisfies the following horn-filling condition: for every nonzero `n : ℕ` and `0 ≤ i ≤ n`, every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.
- `HahnSeries.embDomain` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | Extends the domain of a `HahnSeries` by an `OrderEmbedding`.

### Query: `Fringe Brightness`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `εNFA.evalFrom` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element of `S`.

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
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `Mathlib.Notation3.foldKind` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.Kind` (Mathlib)
- `Mathlib.Tactic.ITauto.AndKind` (Mathlib)
- `SSet.relativeCellComplex` (Mathlib)
- `Topology.RelCWComplex.closedCell` (Mathlib)
- `Topology.CWComplex.cell_def` (Mathlib)
- `SSet.Quasicategory.hornFilling` (Mathlib)
- `SSet.KanComplex.hornFilling` (Mathlib)
- `HahnSeries.embDomain` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `εNFA.evalFrom` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0250.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.BeamLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.CellState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.FigureElement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.FillingProtocol`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.FringeBrightness`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.FringeShiftPattern`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.HasStatedProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.HasVacuumReferenceIndex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.InterferometerArm`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.IsNearestHundredThousandthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.LaserKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.MatchesSourceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.MichelsonGasCellExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.ObeysCompleteFringeShiftLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.ObeysRoundTripOpticalPathLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0250.PropagationDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

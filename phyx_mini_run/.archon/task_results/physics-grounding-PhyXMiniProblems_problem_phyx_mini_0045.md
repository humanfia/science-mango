# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0045.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0045.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:69f6c5d0206f7e8c85d3ad824a93735de08b22d424e1c72ca23177669caeafca
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

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Thin Lens Kind`
- `CategoryTheory.ThinSkeleton` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | Construct the skeleton category by taking the quotient of objects. This construction gives a preorder with nice definitional properties, but is only really appropriate for thin categories. If your original category is...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.ThinSkeleton.thin` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | The thin skeleton is thin.

### Query: `Eyeglass Lens`
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.get_rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Row Length Consistency.** For a Young diagram $\mu$, the $i$-th element of the list of row lengths $\mu.\text{rowLens}$ is equal to the length of the $i$-th row $\mu.\text{rowLen } i$, provided that $i$ is a valid i...

### Query: `Object Location`
- `CategoryTheory.ObjectProperty` | module `Mathlib.CategoryTheory.ObjectProperty.Basic` | package Mathlib | A property of objects in a category `C` is a predicate `C → Prop`.
- `Lean.Name.location` | module `Physlib.Meta.Basic` | package PhysLean | Returns the location of a name.
- `CategoryTheory.GradedObject` | module `Mathlib.CategoryTheory.GradedObject` | package Mathlib | A type synonym for `β → C`, used for `β`-graded objects in a category `C`.

### Query: `Incident Ray Geometry`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `SimpleGraph.otherVertexOfIncident` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | Given an edge incident to a particular vertex, get the other vertex on the edge.
- `SimpleGraph.incMatrix_of_notMem_incidenceSet` | module `Mathlib.Combinatorics.SimpleGraph.IncMatrix` | package Mathlib | **Incidence Matrix Entry for Non-Incident Vertex and Edge.** For a simple graph $G$ and a ring $R$, if an edge $e$ is not incident to a vertex $a$, then the entry of the incidence matrix of $G$ at row $a$ and column $...

### Query: `Myopic Eye`
- `CategoryTheory.Over.isMono` | module `Mathlib.CategoryTheory.Subobject.MonoOver` | package Mathlib | The object property in `Over X` of the structure morphism being a monomorphism.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Eyeglass Correction Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `CategoryTheory.ThinSkeleton` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.thin` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.get_rowLens` (Mathlib)
- `CategoryTheory.ObjectProperty` (Mathlib)
- `Lean.Name.location` (PhysLean)
- `CategoryTheory.GradedObject` (Mathlib)
- `SameRay` (Mathlib)
- `SimpleGraph.otherVertexOfIncident` (Mathlib)
- `SimpleGraph.incMatrix_of_notMem_incidenceSet` (Mathlib)
- `CategoryTheory.Over.isMono` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `HahnSeries.single` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0045.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.EyeglassCorrectionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.EyeglassLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.FormsVirtualImageAtFarPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.HasPhysicalAxialPlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.HasStatedDistanceReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.IncidentRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.MyopicEye`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.ObeysParallelRayFocalLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.ObjectLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0045.ThinLensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

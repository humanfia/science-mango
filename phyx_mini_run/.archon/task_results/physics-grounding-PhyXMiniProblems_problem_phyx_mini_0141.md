# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0141.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0141.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:97009b506e9691bfacd515ace3a4aa6ab18984b1a07db7bd9b7aece5a0e4e2ab
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

### Query: `metre Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `UnitChoices.ext_iff` | module `Physlib.Units.Basic` | package PhysLean | **Equality of Unit Choices.** Two systems of unit choices are equal if and only if their respective units for length, time, mass, charge, and temperature are all identical.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Diagram Point`
- `Mathlib.Tactic.Widget.StringDiagram.Node` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Nodes in a string diagram.
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `Profinite.diagram'` | module `Mathlib.Topology.Category.Profinite.Extend` | package Mathlib | An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Figure Ray Part`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Set.image_subtype_val_Iic_Ici` | module `Mathlib.Order.Interval.Set.Image` | package Mathlib | **Image of a Closed Ray in a Subtype.** For any element $a$ in a partially ordered set, let $I_{ic}(a)$ denote the subtype of elements less than or equal to $a$. For any $b$ in this subtype, the image of the closed up...

### Query: `start Point`
- `Path.source_mem_range` | module `Mathlib.Topology.Path` | package Mathlib | **Source Point in Path Range.** For any path $\gamma$ from $x$ to $y$ in a topological space, the starting point $x$ is contained in the range of $\gamma$.
- `DFA.union_start` | module `Mathlib.Computability.DFA` | package Mathlib | **Initial State of the Union DFA.** The starting state of the union of two deterministic finite automata $M_1$ and $M_2$ is the ordered pair consisting of the starting state of $M_1$ and the starting state of $M_2$.
- `Path.source` | module `Mathlib.Topology.Path` | package Mathlib | **Starting Point of a Path.** For any path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the start of the unit interval, $\gamma(0)$, is equal to the initial point $x$.

### Query: `end Point`
- `Function.End` | module `Mathlib.Algebra.Group.End` | package Mathlib | The monoid of endomorphisms. Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`.
- `Module.End` | module `Mathlib.Algebra.Module.LinearMap.End` | package Mathlib | Linear endomorphisms of a module, with associated ring structure `Module.End.semiring` and algebra structure `Module.End.algebra`.
- `AddCircle.EndpointIdent` | module `Mathlib.Topology.Instances.AddCircle.Defs` | package Mathlib | The relation identifying the endpoints of `Icc a (a + p)`.

### Query: `Full Body Plane Mirror Diagram`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `CategoryTheory.OrthogonalReflection.D₁.l` | module `Mathlib.CategoryTheory.Presentable.OrthogonalReflection` | package Mathlib | Considering all diagrams consisting of a morphism `f : X ⟶ Y` satisfying `W` and of a morphism `d : X ⟶ Z`, this is the morphism from the coproduct of all these `X` objects to `Z` given by these morphisms `d`.
- `Submodule.reflection` | module `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` | package Mathlib | Reflection in a complete subspace of an inner product space. The word "reflection" is sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes more generally to cover operation...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `UnitChoices.ext_iff` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Mathlib.Tactic.Widget.StringDiagram.Node` (Mathlib)
- `OnePoint` (Mathlib)
- `Profinite.diagram'` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Set.image_subtype_val_Iic_Ici` (Mathlib)
- `Path.source_mem_range` (Mathlib)
- `DFA.union_start` (Mathlib)
- `Path.source` (Mathlib)
- `Function.End` (Mathlib)
- `Module.End` (Mathlib)
- `AddCircle.EndpointIdent` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `CategoryTheory.OrthogonalReflection.D₁.l` (Mathlib)
- `Submodule.reflection` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0141.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.DiagramPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.FigureRayPart`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.FullBodyPlaneMirrorDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.IsVirtualImageAcrossVerticalMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0141.ObeysIdealPlaneMirrorOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

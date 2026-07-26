# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0109.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0109.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a3261ff5ed010582ace48f26faa73d23fbc40f352e744e8017b66ee834b2629d
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

### Query: `Lens Approximation`
- `bernsteinApproximation` | module `Mathlib.Analysis.SpecialFunctions.Bernstein` | package Mathlib | The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials, given by `∑ k, bernstein n k x • f (k/n)`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Filter.IsApproximateUnit.mono` | module `Mathlib.Topology.ApproximateUnit` | package Mathlib | If `l` is an approximate unit and `⊥ < l' ≤ l`, then `l'` is also an approximate unit.

### Query: `Optic Axis Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle between two vectors is `π` if and only if the angle with the vectors swapped is `π`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Vertical Scale Status`
- `Complex.HadamardThreeLines.scale_id_mem_verticalStrip_of_mem_verticalStrip` | module `Mathlib.Analysis.Complex.Hadamard` | package Mathlib | The transformation on ℂ that is used for `scale` maps the strip ``re ⁻¹' (l, u)`` to the strip ``re ⁻¹' (0, 1)``.
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` | module `Mathlib.CategoryTheory.Functor.TwoSquare` | package Mathlib | Notation for the vertical identity 2-square.
- `Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip` | module `Mathlib.Analysis.Complex.Hadamard` | package Mathlib | If z is on the closed strip `re ⁻¹' [l, u]`, then `(z - l) / (u - l)` is on the closed strip `re ⁻¹' [0, 1]`.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Figure Ray Part`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Set.image_subtype_val_Iic_Ici` | module `Mathlib.Order.Interval.Set.Image` | package Mathlib | **Image of a Closed Ray in a Subtype.** For any element $a$ in a partially ordered set, let $I_{ic}(a)$ denote the subtype of elements less than or equal to $a$. For any $b$ in this subtype, the image of the closed up...

### Query: `Principal Ray Lens Diagram`
- `Filter.principal` | module `Mathlib.Order.Filter.Defs` | package Mathlib | The principal filter of `s` is the collection of all supersets of `s`.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

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
- `bernsteinApproximation` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Filter.IsApproximateUnit.mono` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation.oangle_eq_pi_iff_oangle_rev_eq_pi` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `Complex.HadamardThreeLines.scale_id_mem_verticalStrip_of_mem_verticalStrip` (Mathlib)
- `CategoryTheory.TwoSquare.«term𝟙ᵥ»` (Mathlib)
- `Complex.HadamardThreeLines.mem_verticalClosedStrip_of_scale_id_mem_verticalClosedStrip` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Set.image_subtype_val_Iic_Ici` (Mathlib)
- `Filter.principal` (Mathlib)
- `LightDiagram'` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0109.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.FigureRayPart`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.HasCalibratedHorizontalGrid`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.HasPhysicalLengthMagnitudes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.LensApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.MatchesAnswerExactly`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.ObeysThinLensPrincipalRayLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.OpticAxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.PrincipalRayLensDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0109.VerticalScaleStatus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

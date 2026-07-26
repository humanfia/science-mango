# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0138.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0138.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7240358092a428bb7ec4e414a6297eb5a743a78901edbbd2e5ffcda649a0dbfe
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

### Query: `Diagram Point`
- `Mathlib.Tactic.Widget.StringDiagram.Node` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Nodes in a string diagram.
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `Profinite.diagram'` | module `Mathlib.Topology.Category.Profinite.Extend` | package Mathlib | An abbreviation for `S.fintypeDiagram' ⋙ toProfinite`.

### Query: `Diagram Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Display the string diagram for a given term. Example usage: ``` /- String diagram for the equality theorem. -/ #string_diagram MonoidalCategory.whisker_exchange /- String diagram for the morphism. -/ variable {C : Typ...
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Help function for displaying two string diagrams in an equality.

### Query: `Medium Kind`
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` | module `Mathlib.CategoryTheory.Abelian.Preradical.Colon` | package Mathlib | **The Middle Object of the Short Complex Associated with a Preradical.** For any object $X$ in a category $\mathcal{C}$, the middle object (at index 2) of the short complex associated with a preradical is defined as t...
- `Rep.coinvariantsShortComplex_X₂` | module `Mathlib.RepresentationTheory.Coinvariants` | package Mathlib | **The Middle Object of the Coinvariants Short Complex.** For a representation $A$ of a group $G$ over a ring $k$ and a normal subgroup $S \trianglelefteq G$, the middle object $X_2$ of the associated short complex of...
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` | module `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | package Mathlib | **Middle Object of the Short Complex $L_2'$.** The middle object of the short complex $L_2'$ is defined as the first object of the short complex $L_3$ in the given snake input.

### Query: `Medium Region`
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Slab Face`
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.SimplicialObject.δ` | module `Mathlib.AlgebraicTopology.SimplicialObject.Basic` | package Mathlib | Face maps for a simplicial object.
- `Geometry.SimplicialComplex.not_facet_iff_subface` | module `Mathlib.Analysis.Convex.SimplicialComplex.Basic` | package Mathlib | **Characterization of Non-Facet Faces.** For any face $s$ of a simplicial complex $K$, $s$ is not a facet if and only if it is a proper subset of some other face $t$ in $K$.

### Query: `Ray Label`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `Ray Style`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.
- `RayVector.coe` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | **Ray Vector Coercion.** For a ring $R$ and a type $M$ with a zero element, there is a natural coercion from the type of ray vectors $\text{RayVector}(R, M)$ to the underlying type $M$. This coercion maps a ray vector...

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
- `Mathlib.Tactic.Widget.StringDiagram.Node` (Mathlib)
- `OnePoint` (Mathlib)
- `Profinite.diagram'` (Mathlib)
- `SameRay` (Mathlib)
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` (Mathlib)
- `CategoryTheory.Abelian.Preradical.shortComplexObj_X₂` (Mathlib)
- `Rep.coinvariantsShortComplex_X₂` (Mathlib)
- `CategoryTheory.ShortComplex.SnakeInput.L₂'_X₂` (Mathlib)
- `regionBetween` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.SimplicialObject.δ` (Mathlib)
- `Geometry.SimplicialComplex.not_facet_iff_subface` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Module.Ray` (Mathlib)
- `SameRay` (Mathlib)
- `Module.Ray` (Mathlib)
- `RayVector.coe` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0138.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.DiagramPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.DiagramRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.FigureColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.IsPhysicalRefractionAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.IsUniqueMatchingDisplayedSine`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.MatchesDisplayedSineToNearestThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.MediumKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.MediumRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.ParallelGlassSlabSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.RayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.RayStyle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.SatisfiesPlaneParallelGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.SatisfiesSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.SlabFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.SlabModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0138.SnellLawAtInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

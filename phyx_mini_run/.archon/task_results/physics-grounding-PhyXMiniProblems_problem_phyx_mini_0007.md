# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0007.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0007.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:2a62a04ef2411c7145b701faa6b683f124368d3f40f0acf4fab197be3cbb8c6e
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Air Glass Ray Diagram`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Help function for displaying two string diagrams in an equality.
- `Mathlib.Tactic.Widget.StringDiagram.dsl` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Penrose dsl file for string diagrams.

### Query: `incidence Angle eq arctan glass Refractive Index`
- `Real.arctan` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` | package Mathlib | Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and `arctan x < π / 2`
- `Real.arctan_eq_arcsin` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` | package Mathlib | **Arctangent in terms of Arcsine.** For any real number $x$, the arctangent of $x$ is equal to the arcsine of the ratio of $x$ to the square root of $1 + x^2$: $$\arctan x = \arcsin \left( \frac{x}{\sqrt{1 + x^2}} \ri...
- `InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle` | package Mathlib | An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `SameRay` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.mkEqHtml` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.dsl` (Mathlib)
- `Real.arctan` (Mathlib)
- `Real.arctan_eq_arcsin` (Mathlib)
- `InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0007.AirGlassRayDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

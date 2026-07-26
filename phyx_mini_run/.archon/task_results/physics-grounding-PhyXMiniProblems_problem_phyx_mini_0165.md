# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0165.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0165.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Gauss law divergence electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Space.distDiv_inv_pow_eq_dim` | module `Physlib.SpaceAndTime.Space.Norm.Basic` | package PhysLean | The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`) equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the Dirac delta at the origin....

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `millimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).

### Query: `millimeters Value`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).

### Query: `Lens Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `YoungDiagram.get_rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | **Row Length Consistency.** For a Young diagram $\mu$, the $i$-th element of the list of row lengths $\mu.\text{rowLens}$ is equal to the length of the $i$-th row $\mu.\text{rowLen } i$, provided that $i$ is a valid i...

### Query: `Thin Lens Kind`
- `CategoryTheory.ThinSkeleton` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | Construct the skeleton category by taking the quotient of objects. This construction gives a preorder with nice definitional properties, but is only really appropriate for thin categories. If your original category is...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.ThinSkeleton.thin` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | The thin skeleton is thin.

### Query: `Thin Lens`
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` | module `Mathlib.CategoryTheory.FinCategory.Basic` | package Mathlib | **Finite Category Instance for Thin Categories. Let $J$ be a small category that is thin (meaning there is at most one morphism between any two objects). If the set of objects in $J$ is finite, then $J$ is a finite ca...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Imaging Stage`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.order_eq_orderTop_of_ne_zero` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | **Equivalence of Hahn Series Orders for Non-zero Series.** For any non-zero Hahn series $x$, the order of $x$ is equal to its order in the sense of the extended order (where the order of the zero series is defined as...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Space.distDiv_inv_pow_eq_dim` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `YoungDiagram.get_rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.thin` (Mathlib)
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.order_eq_orderTop_of_ne_zero` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0165.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.HasLabeledAxisGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.HasPhysicalSignConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.HasStatedCameraData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.ImagingStage`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.IsNearestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.LensLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.MatchesDisplayedFocalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.MatchesPrimaryRayDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.ObeysSignedThinLensEquationAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.ThinLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.ThinLensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0165.TwoLensCameraSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

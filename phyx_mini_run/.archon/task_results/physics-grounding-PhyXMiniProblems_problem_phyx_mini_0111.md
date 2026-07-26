# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0111.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0111.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e5c69bc9696505a0810c6fb89e1fae0d94c738f799be623aab4ae745178358a8
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

### Query: `centimeters Value`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `Lens Role`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Thin Lens Kind`
- `CategoryTheory.ThinSkeleton` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | Construct the skeleton category by taking the quotient of objects. This construction gives a preorder with nice definitional properties, but is only really appropriate for thin categories. If your original category is...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.ThinSkeleton.thin` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | The thin skeleton is thin.

### Query: `Thin Lens`
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` | module `Mathlib.CategoryTheory.FinCategory.Basic` | package Mathlib | **Finite Category Instance for Thin Categories. Let $J$ be a small category that is thin (meaning there is at most one morphism between any two objects). If the set of objects in $J$ is finite, then $J$ is a finite ca...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Conjugate Location`
- `Matrix.conjTranspose` | module `Mathlib.LinearAlgebra.Matrix.ConjTranspose` | package Mathlib | The conjugate transpose of a matrix defined in term of `star`.
- `Lean.Name.location` | module `Physlib.Meta.Basic` | package PhysLean | Returns the location of a name.
- `CategoryTheory.Bicategory.conjugateEquiv_apply` | module `Mathlib.CategoryTheory.Bicategory.Adjunction.Mate` | package Mathlib | **Conjugate Equivalence via Mates.** Given two adjunctions $l_1 \dashv r_1$ and $l_2 \dashv r_2$ in a bicategory, the conjugate 2-morphism of a 2-morphism $\alpha : l_2 \to l_1$ is defined by applying the mate corresp...

### Query: `Image Nature`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `Finset.image` | module `Mathlib.Data.Finset.Image` | package Mathlib | `image f s` is the forward image of `s` under `f`.
- `Fin.finsetImage_val_Ico` | module `Mathlib.Order.Interval.Finset.Fin` | package Mathlib | **Image of a Finite Interval of Bounded Natural Numbers.** The image of the left-closed, right-open interval $[a, b)$ in the type of natural numbers less than $n$ under the natural inclusion map into $\mathbb{N}$ is e...

### Query: `Image Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Orientation.rotation_rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | Rotating twice is equivalent to rotating by the sum of the angles.

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
- `LengthUnit.centimeters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.thin` (Mathlib)
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `Matrix.conjTranspose` (Mathlib)
- `Lean.Name.location` (PhysLean)
- `CategoryTheory.Bicategory.conjugateEquiv_apply` (Mathlib)
- `Set.image` (Mathlib)
- `Finset.image` (Mathlib)
- `Fin.finsetImage_val_Ico` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Orientation.rotation_rotation` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0111.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.AxialFigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.ConjugateLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.GalileanTelescopeSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.HasObjectiveFocalLengthCalibration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.HasPhysicalGalileanParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.ImageNature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.ImageOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.IsNearestTenthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.LensRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.MatchesAngularMagnificationReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.MatchesGalileanTelescopeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.RayDirectionLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.SatisfiesAfocalGalileanLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.ThinLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0111.ThinLensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

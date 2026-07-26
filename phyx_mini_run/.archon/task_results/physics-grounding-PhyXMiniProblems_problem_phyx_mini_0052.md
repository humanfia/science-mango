# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0052.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0052.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f083b8fce62651a8f56c37c9007bc8b39a183d7b02d38b5eb3c17977c875a0a3
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

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `centimeters Value`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `Thin Lens Kind`
- `CategoryTheory.ThinSkeleton` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | Construct the skeleton category by taking the quotient of objects. This construction gives a preorder with nice definitional properties, but is only really appropriate for thin categories. If your original category is...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.ThinSkeleton.thin` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | The thin skeleton is thin.

### Query: `Image Nature`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `Finset.image` | module `Mathlib.Data.Finset.Image` | package Mathlib | `image f s` is the forward image of `s` under `f`.
- `Fin.finsetImage_val_Ico` | module `Mathlib.Order.Interval.Finset.Fin` | package Mathlib | **Image of a Finite Interval of Bounded Natural Numbers.** The image of the left-closed, right-open interval $[a, b)$ in the type of natural numbers less than $n$ under the natural inclusion map into $\mathbb{N}$ is e...

### Query: `Image Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation` | module `Mathlib.LinearAlgebra.Orientation` | package Mathlib | An orientation of a module, intended to be used when `ι` is a `Fintype` with the same cardinality as a basis.
- `Orientation.rotation_rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | Rotating twice is equivalent to rotating by the sum of the angles.

### Query: `Magnifying Glass Diagram`
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...
- `CategoryTheory.GlueData.diagram` | module `Mathlib.CategoryTheory.GlueData` | package Mathlib | (Implementation) The diagram to take colimit of.
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Display the string diagram for a given term. Example usage: ``` /- String diagram for the equality theorem. -/ #string_diagram MonoidalCategory.whisker_exchange /- String diagram for the morphism. -/ variable {C : Typ...

### Query: `Has Stated Problem Data`
- `CategoryTheory.ShortComplex.LeftHomologyData.ofHasCokernel` | module `Mathlib.Algebra.Homology.ShortComplex.LeftHomology` | package Mathlib | When the second map `S.g` is zero, this is the left homology data on `S` given by the chosen `cokernel S.f`
- `CategoryTheory.ShortComplex.RightHomologyData.ofHasKernel` | module `Mathlib.Algebra.Homology.ShortComplex.RightHomology` | package Mathlib | When the first map `S.f` is zero, this is the right homology data on `S` given by the chosen `kernel S.g`
- `Mathlib.PrintSorries.State` | module `Mathlib.Util.PrintSorries` | package Mathlib | Type of intermediate computation of sorry-tracking.

### Query: `Has Positive Problem Lengths`
- `List.splitLengths` | module `Mathlib.Data.List.SplitLengths` | package Mathlib | Split a list to chunks of given lengths.
- `IsStrictlyPositive` | module `Mathlib.Algebra.Algebra.StrictPositivity` | package Mathlib | An element of an ordered algebra is *strictly positive* if it is nonnegative and invertible. NOTE: This definition will be generalized to the non-unital case in the future; do not unfold the definition and use the API...
- `Composition.length_pos_iff` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | **Positivity of Composition Length.** For a composition of a natural number $n$, the length of the composition is strictly positive if and only if $n$ is strictly positive.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `CategoryTheory.ThinSkeleton` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.thin` (Mathlib)
- `Set.image` (Mathlib)
- `Finset.image` (Mathlib)
- `Fin.finsetImage_val_Ico` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation` (Mathlib)
- `Orientation.rotation_rotation` (Mathlib)
- `YoungDiagram` (Mathlib)
- `CategoryTheory.GlueData.diagram` (Mathlib)
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` (Mathlib)
- `CategoryTheory.ShortComplex.LeftHomologyData.ofHasCokernel` (Mathlib)
- `CategoryTheory.ShortComplex.RightHomologyData.ofHasKernel` (Mathlib)
- `Mathlib.PrintSorries.State` (Mathlib)
- `List.splitLengths` (Mathlib)
- `IsStrictlyPositive` (Mathlib)
- `Composition.length_pos_iff` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0052.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.HasDisplayedImageLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.HasPositiveProblemLengths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.HasStatedProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.ImageNature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.ImageOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.IsCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.MagnifyingGlassDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.MatchesRayDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.ObeysThinLensEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.ObeysTransverseMagnificationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.ThinLensKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0052.UsesCartesianSignConvention`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

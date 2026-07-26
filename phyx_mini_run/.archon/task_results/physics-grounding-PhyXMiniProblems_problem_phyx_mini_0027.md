# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0027.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0027.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Object Corner`
- `Subsemigroup.corner` | module `Mathlib.RingTheory.Idempotents` | package Mathlib | The corner associated to an element `e` in a semigroup is the subsemigroup of all elements of the form `e * r * e`.
- `CategoryTheory.ObjectProperty` | module `Mathlib.CategoryTheory.ObjectProperty.Basic` | package Mathlib | A property of objects in a category `C` is a predicate `C → Prop`.
- `BoxIntegral.Box.upper_mem` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | **Upper Corner Membership.** The upper corner of a rectangular box $I$ is an element of $I$.

### Query: `Image Corner`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `ModelWithCorners.image_eq` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | **Image of a Model with Corners.** For a model with corners $I$ and any subset $s$ of its domain, the image of $s$ under $I$ is equal to the intersection of the range of $I$ and the preimage of $s$ under the inverse m...
- `isCorner_image` | module `Mathlib.Combinatorics.Additive.Corner.Defs` | package Mathlib | **Invariance of Corners under Freiman Isomorphisms.** Let $f: s \to t$ be an additive $2$-Freiman isomorphism. For any subset $A \subseteq s \times s$ and elements $x_1, y_1, x_2, y_2 \in s$, the points $(x_1, y_1), (...

### Query: `corresponding Image`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `Finset.image` | module `Mathlib.Data.Finset.Image` | package Mathlib | `image f s` is the forward image of `s` under `f`.
- `Relation.Map` | module `Mathlib.Logic.Relation` | package Mathlib | The map of a relation `r` through a pair of functions pushes the relation to the codomains of the functions. The resulting relation is defined by having pairs of terms related if they have preimages related by `r`.

### Query: `Thin Lens Square Setup`
- `Mathlib.Tactic.Widget.commutativeSquarePresenter` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Presenter for a commutative square
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Has Physical Real Image Configuration`
- `Configuration.HasPoints` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of lines has an intersection point.
- `Real` | module `Mathlib.Data.Real.Basic` | package Mathlib | The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational numbers.
- `Configuration.HasLines` | module `Mathlib.Combinatorics.Configuration` | package Mathlib | A nondegenerate configuration in which every pair of points has a line through them.

### Query: `Matches Figure Readouts`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Respects Labeled Image Planes`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` | module `Physlib.QFT.QED.AnomalyCancellation.Even.BasisLinear` | package PhysLean | **Orthogonality of Basis Charges and Even-Indexed Planes.** For any two distinct indices $k$ and $j$ in $\{0, \dots, n\}$, the $k$-th basis charge evaluated on the first vector of the $j$-th even plane is zero.
- `CategoryTheory.MorphismProperty.RespectsIso.inverseImage` | module `Mathlib.CategoryTheory.MorphismProperty.Basic` | package Mathlib | **Stability of Inverse Image Properties under Isomorphisms.** If a property of morphisms in a category $D$ respects isomorphisms, then for any functor $F : C \to D$, the inverse image of this property under $F$ also r...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Subsemigroup.corner` (Mathlib)
- `CategoryTheory.ObjectProperty` (Mathlib)
- `BoxIntegral.Box.upper_mem` (Mathlib)
- `Set.image` (Mathlib)
- `ModelWithCorners.image_eq` (Mathlib)
- `isCorner_image` (Mathlib)
- `Set.image` (Mathlib)
- `Finset.image` (Mathlib)
- `Relation.Map` (Mathlib)
- `Mathlib.Tactic.Widget.commutativeSquarePresenter` (Mathlib)
- `IsSquare` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `Configuration.HasPoints` (Mathlib)
- `Real` (Mathlib)
- `Configuration.HasLines` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `Set.image` (Mathlib)
- `PureU1.VectorLikeEvenPlane.basis_on_evenFst_other` (PhysLean)
- `CategoryTheory.MorphismProperty.RespectsIso.inverseImage` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0027.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.HasPhysicalRealImageConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.ImageCorner`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.ObjectCorner`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.RespectsLabeledImagePlanes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.SatisfiesThinLensEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.SatisfiesTransverseMagnification`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0027.ThinLensSquareSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

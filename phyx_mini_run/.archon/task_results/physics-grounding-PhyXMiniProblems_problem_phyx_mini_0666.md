# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0666.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0666.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:872b8e5ffadcdf45942f6ef837c87d9be213b7d95ceb74f824be2e8ef1c51993
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

### Query: `area In Square Meters`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.

### Query: `Frustum Figure Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `WriterT.mkLabel'` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Lifting Labels to the Writer Monad Transformer.** Given a monoid $\omega$, a label for a computation in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be transformed into a label for a computa...

### Query: `Frustum Figure Feature`
- `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit_π_app` | module `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers` | package Mathlib | **Construction of a Cone from a Fork.** Given a functor $F : J \to \mathcal{C}$, let $c_1$ be a fan over the objects $F(j)$ for $j \in J$, and $c_2$ be a fan over the objects $F(\text{codomain}(f))$ for all morphisms...
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `CategoryTheory.Limits.Cone` | module `Mathlib.CategoryTheory.Limits.Cones` | package Mathlib | A `c : Cone F` is: * an object `c.pt` and * a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to `F`. Example: if `J` is a category coming from a poset then the data required to make a term of...

### Query: `Supplied Frustum Figure`
- `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit_π_app` | module `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers` | package Mathlib | **Construction of a Cone from a Fork.** Given a functor $F : J \to \mathcal{C}$, let $c_1$ be a fan over the objects $F(j)$ for $j \in J$, and $c_2$ be a fan over the objects $F(\text{codomain}(f))$ for all morphisms...
- `Finset.sup` | module `Mathlib.Data.Finset.Lattice.Fold` | package Mathlib | Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c`
- `Finset.truncatedSup` | module `Mathlib.Combinatorics.SetFamily.AhlswedeZhang` | package Mathlib | The supremum of the elements of `s` less than `a` if there are some, otherwise `⊤`.

### Query: `Right Circular Conical Frustum`
- `CircularOrder` | module `Mathlib.Order.Circular` | package Mathlib | A circular order is the analogue of a linear order where you can loop around. `≤` and `<` are replaced by ternary relations `btw` and `sbtw`. `btw` is reflexive, cyclic, antisymmetric and total. `sbtw` is transitive.
- `CategoryTheory.Limits.Cone` | module `Mathlib.CategoryTheory.Limits.Cones` | package Mathlib | A `c : Cone F` is: * an object `c.pt` and * a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to `F`. Example: if `J` is a category coming from a poset then the data required to make a term of...
- `CategoryTheory.Limits.coneRightOpOfCocone_pt` | module `Mathlib.CategoryTheory.Limits.Cones` | package Mathlib | **Cone from a Cocone via the Right Opposite Functor.** Given a functor $F : J^{\text{op}} \to C$, the tip of the cone over the right opposite functor $F^{\text{rightOp}} : J \to C^{\text{op}}$ obtained from a cocone o...

### Query: `Matches Supplied Frustum Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Has Valid Frustum Parameters`
- `Ordnode.Valid'` | module `Mathlib.Data.Ordmap.Ordset` | package Mathlib | The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are correct, the tree is balanced, and the elements of the tree are organized according to the ordering. This version of `Valid` als...
- `Ordnode.Valid` | module `Mathlib.Data.Ordmap.Ordset` | package Mathlib | The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are correct, the tree is balanced, and the elements of the tree are organized according to the ordering.
- `Ordnode.Valid'.valid` | module `Mathlib.Data.Ordmap.Ordset` | package Mathlib | **Validity of Bounded Ordered Nodes.** If an ordered tree is valid within a specific open interval $(o_1, o_2)$, then it is a valid ordered tree; that is, it satisfies the required balancing invariants, every node cor...

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
- `IsSquare` (Mathlib)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `DimArea.squareMeter` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `WriterT.mkLabel'` (Mathlib)
- `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit_π_app` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `CategoryTheory.Limits.Cone` (Mathlib)
- `CategoryTheory.Limits.HasLimitOfHasProductsOfHasEqualizers.buildLimit_π_app` (Mathlib)
- `Finset.sup` (Mathlib)
- `Finset.truncatedSup` (Mathlib)
- `CircularOrder` (Mathlib)
- `CategoryTheory.Limits.Cone` (Mathlib)
- `CategoryTheory.Limits.coneRightOpOfCocone_pt` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `Ordnode.Valid'` (Mathlib)
- `Ordnode.Valid` (Mathlib)
- `Ordnode.Valid'.valid` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0666.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.FrustumFigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.FrustumFigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.HasValidFrustumParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.MatchesSuppliedFrustumFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.RightCircularConicalFrustum`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.SatisfiesFrustumCurvedSurfaceAreaLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.SatisfiesRightFrustumMeridianGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0666.SuppliedFrustumFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

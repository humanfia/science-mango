# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0080.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0080.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:053229a7d2de3d1a9651809c1b683509310ebcee8bb0ed62c409aa14e6f41b8d
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

### Query: `length Value In`
- `LengthUnit.val_ne_zero` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Non-zero Length Unit.** For any length unit, its associated numerical value is non-zero.
- `LengthUnit.instInhabited` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | **Default Length Unit.** The type of length units is inhabited, with a default value defined as the positive real number $1$.
- `Computation.length_pure` | module `Mathlib.Data.Seq.Computation` | package Mathlib | **Length of a Pure Computation.** The length of a pure computation of a value $a$ is equal to $0$.

### Query: `nanometers Value`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.
- `spectralValue` | module `Mathlib.Analysis.Normed.Unbundled.SpectralNorm` | package Mathlib | The spectral value of a polynomial in `R[X]`, where `R` is a seminormed ring. One motivation for the spectral value: if the norm on `R` is nonarchimedean, and if a monic polynomial splits into linear factors, then its...

### Query: `degrees As Angle`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are equal.

### Query: `Unit Cell Edge Label`
- `SimpleGraph.EdgeLabeling.labelGraph` | module `Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling` | package Mathlib | Given an edge labeling and a choice of label `k`, construct the graph corresponding to the edges labeled `k`.
- `SimpleGraph.edgeFinset` | module `Mathlib.Combinatorics.SimpleGraph.Finite` | package Mathlib | The `edgeSet` of the graph as a `Finset`.
- `SimpleGraph.edgeSet` | module `Mathlib.Combinatorics.SimpleGraph.Basic` | package Mathlib | `G.edgeSet` is the edge set for `G`. This is an abbreviation for `edgeSetEmbedding G` that permits dot notation.

### Query: `Reflection Plane Family`
- `EuclideanGeometry.reflection_involutive` | module `Mathlib.Geometry.Euclidean.Projection` | package Mathlib | Reflection is involutive.
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...

### Query: `XRay Beam`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `LinearMap.IsReflective` | module `Mathlib.LinearAlgebra.RootSystem.OfBilinear` | package Mathlib | A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is injective, and for any vector `y`, the norm of `x` divides twice the inner product of `x` and `y`. These conditions are what...

### Query: `Square Lattice Crystal`
- `Lattice` | module `Mathlib.Order.Lattice` | package Mathlib | A lattice is a join-semilattice which is also a meet-semilattice.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `LatticeCon` | module `Mathlib.Order.Lattice.Congruence` | package Mathlib | An equivalence relation is a congruence relation for the lattice structure if it is compatible with the `inf` and `sup` operations.

### Query: `XRay Diffraction Figure`
- `Mathlib.Tactic.Widget.mkCommDiag` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Construct a commutative diagram from a Penrose `sub`stance program and expressions `embeds` to display as labels in the diagram.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.val_ne_zero` (PhysLean)
- `LengthUnit.instInhabited` (PhysLean)
- `Computation.length_pure` (Mathlib)
- `LengthUnit.nanometers` (PhysLean)
- `AbsoluteValue` (Mathlib)
- `spectralValue` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` (Mathlib)
- `SimpleGraph.EdgeLabeling.labelGraph` (Mathlib)
- `SimpleGraph.edgeFinset` (Mathlib)
- `SimpleGraph.edgeSet` (Mathlib)
- `EuclideanGeometry.reflection_involutive` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `Module.reflection` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `LinearMap.IsReflective` (Mathlib)
- `Lattice` (Mathlib)
- `IsSquare` (Mathlib)
- `LatticeCon` (Mathlib)
- `Mathlib.Tactic.Widget.mkCommDiag` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0080.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.HasPhysicalDiffractionParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.HasStatedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.IsClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.MatchesShownLatticeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.ReflectionObservation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.ReflectionPlaneFamily`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.SatisfiesBraggReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.SatisfiesDiagonalPlaneSpacingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.SquareLatticeCrystal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.UnitCellEdgeLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.XRayBeam`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.XRayCrystalSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0080.XRayDiffractionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

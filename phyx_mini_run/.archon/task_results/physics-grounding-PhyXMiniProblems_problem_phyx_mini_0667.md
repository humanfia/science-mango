# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0667.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0667.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8bfea2f7ecfea42e0ab91bda52298ddd44dd5f3be7d08b68c4790db05ce08668
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

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Cardinal Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Cardinal.instSuccOrder` | module `Mathlib.SetTheory.Cardinal.Order` | package Mathlib | Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`.

### Query: `Car Position`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.positionCLM` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | Component `i` of the position operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Compass Heading`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `HomologicalComplex₂.d₁` | module `Mathlib.Algebra.Homology.TotalComplex` | package Mathlib | The horizontal differential in the total complex on a given summand.

### Query: `due East Heading`
- `Turing.Dir.right` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Right Movement.** One of the two possible directions of travel for a Turing machine head, representing a move to the right.
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.

### Query: `south Of East Heading`
- `Subgroup.subgroupOf` | module `Mathlib.Algebra.Group.Subgroup.Map` | package Mathlib | For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`.
- `Turing.Dir.left` | module `Mathlib.Computability.TuringMachine.Tape` | package Mathlib | **Left Direction.** One of the two possible directions of movement for a Turing machine head.
- `Abelianization.of` | module `Mathlib.GroupTheory.Abelianization.Defs` | package Mathlib | `of` is the canonical projection from G to its abelianization.

### Query: `Road Shape`
- `ComplexShape` | module `Mathlib.Algebra.Homology.ComplexShape` | package Mathlib | A `c : ComplexShape ι` describes the shape of a chain complex, with chain groups indexed by `ι`. Typically `ι` will be `ℕ`, `ℤ`, or `Fin n`. There is a relation `Rel : ι → ι → Prop`, and we will only allow a non-zero...
- `CategoryTheory.Limits.HasLimitsOfShape` | module `Mathlib.CategoryTheory.Limits.HasLimits` | package Mathlib | `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`.
- `Mathlib.Tactic.MkIff.Shape` | module `Mathlib.Tactic.MkIffOfInductiveProp` | package Mathlib | Auxiliary data associated with a single constructor of an inductive declaration.

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
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Cardinal.instSuccOrder` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.positionCLM` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `HomologicalComplex₂.d₁` (Mathlib)
- `Turing.Dir.right` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `Turing.Dir.left` (Mathlib)
- `Subgroup.subgroupOf` (Mathlib)
- `Turing.Dir.left` (Mathlib)
- `Abelianization.of` (Mathlib)
- `ComplexShape` (Mathlib)
- `CategoryTheory.Limits.HasLimitsOfShape` (Mathlib)
- `Mathlib.Tactic.MkIff.Shape` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0667.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.CarPosition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.CardinalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.CompassHeading`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.HasPhysicalCurveParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.HighwayCurveDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.HighwayCurveSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.MatchesAnswerToNearestTenMeters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.RoadShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.SatisfiesCircularArcLengthLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0667.SatisfiesCircularTangentGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0048.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0048.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:95c6221a2783ea25f0370da38f2c1fdf93804909f0bc8b7b2b0f27a2743d6c30
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

### Query: `metres`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `MetricSpace` | module `Mathlib.Topology.MetricSpace.Defs` | package Mathlib | A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying `dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality `dist x z ≤ dist x y + dist y z`. See pseudometric...

### Query: `si Metres`
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.

### Query: `degrees`
- `Polynomial.natDegree` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Polynomial.natDegree_eq_of_degree_eq` | module `Mathlib.Algebra.Polynomial.Degree.Defs` | package Mathlib | **Equality of Natural Degrees from Equality of Degrees.** For any two polynomials $p$ and $q$ over a semiring $S$, if their degrees are equal, then their natural degrees are also equal.

### Query: `Auxiliary Refraction Figure`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `List.argAux_self` | module `Mathlib.Data.List.MinMax` | package Mathlib | **Self-Argument of the Auxiliary Argument Function.** For any irreflexive relation $r$ and any element $a$, the auxiliary argument function `argAux` applied to the current best value $a$ and the element $a$ itself ret...
- `CategoryTheory.Comma.limitAuxiliaryCone` | module `Mathlib.CategoryTheory.Limits.Comma` | package Mathlib | (Implementation). An auxiliary cone which is useful in order to construct limits in the comma category.

### Query: `Matches Auxiliary Refraction Figure`
- `Mathlib.Tactic.Translate.findAuxDecls` | module `Mathlib.Tactic.Translate.Core` | package Mathlib | Returns a `NameSet` of auxiliary constants in `decl` that might have been generated when adding `pre` to the environment, and which hence might need to be translated. Examples include `pre.match_5`, `pre._proof_2`, `s...
- `CategoryTheory.Comma.limitAuxiliaryCone` | module `Mathlib.CategoryTheory.Limits.Comma` | package Mathlib | (Implementation). An auxiliary cone which is useful in order to construct limits in the comma category.
- `Mathlib.Linter.AuxLemma.linter.auxLemma` | module `Mathlib.Tactic.Linter.AuxLemma` | package Mathlib | The `auxLemma` linter emits a warning on any explicit reference to an auto-generated auxiliary declaration (such as `_proof_1`, `match_1`, or `_sizeOf_1`). These names are internal to the Lean elaborator and are not s...

### Query: `Obeys Auxiliary Snell Law`
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `CategoryTheory.Comma.colimitAuxiliaryCocone` | module `Mathlib.CategoryTheory.Limits.Comma` | package Mathlib | (Implementation). An auxiliary cocone which is useful in order to construct colimits in the comma category.
- `Mathlib.Linter.Style.linter.oldObtain` | module `Mathlib.Tactic.Linter.OldObtain` | package Mathlib | The `oldObtain` linter emits a warning upon uses of the "stream-of-consciousness" variants of the `obtain` tactic, i.e. with the proof postponed.

### Query: `Dressing Mirror Setup`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.IsReflexivePair.mk'` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **Reflexive Pair Construction.** A pair of parallel morphisms $f, g: A \to B$ is a reflexive pair if there exists a morphism $s: B \to A$ such that $s \gg f = \text{id}_B$ and $s \gg g = \text{id}_B$.

### Query: `mirror Top Height Above Floor`
- `Order.height_top_eq_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Height of the Top Element and Krull Dimension.** In a preorder with a top element $\top$, the height of $\top$ is equal to the Krull dimension of the preorder.
- `Int.floor` | module `Mathlib.Algebra.Order.Floor.Defs` | package Mathlib | `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`.
- `ENat.floor_top` | module `Mathlib.Algebra.Order.Floor.Extended` | package Mathlib | **Floor of Infinity in Extended Naturals.** The floor of the top element (infinity) in the extended natural numbers is equal to infinity.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `MetricSpace` (Mathlib)
- `UnitChoices.SI_length` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `Polynomial.natDegree` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Polynomial.natDegree_eq_of_degree_eq` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `List.argAux_self` (Mathlib)
- `CategoryTheory.Comma.limitAuxiliaryCone` (Mathlib)
- `Mathlib.Tactic.Translate.findAuxDecls` (Mathlib)
- `CategoryTheory.Comma.limitAuxiliaryCone` (Mathlib)
- `Mathlib.Linter.AuxLemma.linter.auxLemma` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `CategoryTheory.Comma.colimitAuxiliaryCocone` (Mathlib)
- `Mathlib.Linter.Style.linter.oldObtain` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.IsReflexivePair.mk'` (Mathlib)
- `Order.height_top_eq_krullDim` (Mathlib)
- `Int.floor` (Mathlib)
- `ENat.floor_top` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0048.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.AuxiliaryRefractionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.DressingMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.HasPhysicalClosetMirrorGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.IsLowerBoundaryRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.IsPhysicalReflectedFloorRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.IsUpperBoundaryRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.MatchesAuxiliaryRefractionFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.MatchesClosetMirrorData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.ObeysAuxiliarySnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.ObeysPlanarMirrorReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0048.ReflectedFloorRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

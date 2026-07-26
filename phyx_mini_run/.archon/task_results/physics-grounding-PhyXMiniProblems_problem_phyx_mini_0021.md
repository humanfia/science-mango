# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0021.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0021.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Layer`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `linter.tacticAnalysis.regressions.omegaToLia` | module `Mathlib.Tactic.TacticAnalysis.Declarations` | package Mathlib | Debug `lia` by identifying places where it does not yet supersede `omega`.

### Query: `Parallel Layer Stack`
- `ProbabilityTheory.Kernel.parallelComp` | module `Mathlib.Probability.Kernel.Composition.ParallelComp` | package Mathlib | Parallel product of two kernels.
- `Computation.parallel` | module `Mathlib.Data.Seq.Parallel` | package Mathlib | Parallel computation of an infinite stream of computations, taking the first result
- `CategoryTheory.Limits.WalkingParallelPair` | module `Mathlib.CategoryTheory.Limits.Shapes.Equalizers` | package Mathlib | The type of objects for the diagram indexing a (co)equalizer.

### Query: `refractive Index Readout`
- `Subgroup.index` | module `Mathlib.GroupTheory.Index` | package Mathlib | The index of a subgroup as a natural number. Returns `0` if the index is infinite. [Wikidata Q1464168](https://www.wikidata.org/wiki/Q1464168)
- `Composition.index` | module `Mathlib.Combinatorics.Enumerative.Composition` | package Mathlib | `c.index j` is the index of the block in the composition `c` containing `j`.
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` | module `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` | package Mathlib | **The Reflexion Morphism.** In the indexing category for reflexive pairs, there exists a morphism, termed the reflexion, from the object $0$ to the object $1$.

### Query: `Upper Stack Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `Module.Ray` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | A ray (equivalence class of nonzero vectors with common positive multiples) in a module.

### Query: `Transmitted Extension`
- `LinearExtension` | module `Mathlib.Order.Extension.Linear` | package Mathlib | A type alias for `α`, intended to extend a partial order on `α` to a linear order.
- `TietzeExtension` | module `Mathlib.Topology.TietzeExtension` | package Mathlib | A class encoding the concept that a space satisfies the Tietze extension property.
- `Equiv.Perm.IsSwap.of_subtype_isSwap` | module `Mathlib.GroupTheory.Perm.Support` | package Mathlib | **Extension of a Transposition from a Subtype.** If a permutation of a subtype $\{x \in \alpha \mid p(x)\}$ is a transposition, then its extension to a permutation of the entire set $\alpha$ (which acts as the identit...

### Query: `radians To Degrees`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Is Physical Ray Angle`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Orientation.angle_eq_iff_oangle_eq_or_sameRay` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | `y` has equal unoriented angles to `x` and `z` if and only if it has equal oriented angles (bisects the angle) or `x` and `z` are on the same ray.
- `Orientation.oangle_eq_zero_iff_sameRay` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle between two vectors is zero if and only if they are on the same ray.

### Query: `Has Physical Upper Angles`
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Real.Angle.toReal_le_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Upper Bound of the Real Representative of an Angle.** For any angle $\theta$, its representative in the interval $(-\pi, \pi]$ is always less than or equal to $\pi$.

### Query: `Satisfies Upper Interface Snell Laws`
- `upperClosure` | module `Mathlib.Order.UpperLower.Closure` | package Mathlib | The greatest upper set containing a given set.
- `instLawfulOrderSup_mathlib` | module `Mathlib.Order.MinMax` | package Mathlib | **Lawful Supremum Order.** In any type equipped with a linear order, the supremum operation (the maximum of two elements) is lawful. Specifically, for any elements $a$, $b$, and $c$, the maximum of $a$ and $b$ is less...
- `PureU1.lineInPlaneCond_eq_last'` | module `Physlib.QFT.QED.AnomalyCancellation.LineInPlaneCond` | package PhysLean | **Linear Solution Symmetry under the Line-in-Plane Condition.** For a linear solution $S$ of the system $PureU1(n+2)$, if $S$ satisfies the line-in-plane condition and the squares of its last two components are distin...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `linter.tacticAnalysis.regressions.omegaToLia` (Mathlib)
- `ProbabilityTheory.Kernel.parallelComp` (Mathlib)
- `Computation.parallel` (Mathlib)
- `CategoryTheory.Limits.WalkingParallelPair` (Mathlib)
- `Subgroup.index` (Mathlib)
- `Composition.index` (Mathlib)
- `CategoryTheory.Limits.WalkingReflexivePair.Hom.reflexion` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `Module.Ray` (Mathlib)
- `LinearExtension` (Mathlib)
- `TietzeExtension` (Mathlib)
- `Equiv.Perm.IsSwap.of_subtype_isSwap` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `SameRay` (Mathlib)
- `Orientation.angle_eq_iff_oangle_eq_or_sameRay` (Mathlib)
- `Orientation.oangle_eq_zero_iff_sameRay` (Mathlib)
- `EuclideanGeometry.oangle` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Real.Angle.toReal_le_pi` (Mathlib)
- `upperClosure` (Mathlib)
- `instLawfulOrderSup_mathlib` (Mathlib)
- `PureU1.lineInPlaneCond_eq_last'` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0021.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.HasPhysicalUpperAngles`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.HasTotalInternalReflectionAtFinalInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.IncidentAnglesProducingFinalTIR`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.IsPhysicalRayAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.MatchesProblemFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.OpticalLayer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.ParallelLayerStack`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.SatisfiesFinalInterfaceSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.SatisfiesUpperInterfaceSnellLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.TransmittedExtension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0021.UpperStackRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

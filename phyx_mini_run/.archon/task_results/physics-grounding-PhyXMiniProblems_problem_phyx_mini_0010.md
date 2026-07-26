# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0010.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0010.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:434b0ef7e2c86df0d5b3a728f1fe1181598c9afaf4d643865a5793bd6bead9fe
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Region`
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `Cylindrical Rod Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PiNat.cylinder` | module `Mathlib.Topology.MetricSpace.PiNat` | package Mathlib | In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted `cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e., such that `y i = x i` for all `i < n`.
- `MeasureTheory.squareCylinders` | module `Mathlib.MeasureTheory.Constructions.Cylinders` | package Mathlib | Given a finite set `s` of indices, a square cylinder is the product of a set `S` of `∀ i : s, α i` and of `univ` on the other indices. The set `S` is a product of sets `t i` such that for all `i : s`, `t i ∈ C i`. `sq...

### Query: `two Micrometers`
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).
- `hyperoperation_two` | module `Mathlib.Data.Nat.Hyperoperation` | package Mathlib | **Hyperoperation of Rank Two.** For any two natural numbers $m$ and $k$, the hyperoperation of rank 2, denoted $H_2(m, k)$, is equal to the product $m \times k$.
- `TimeUnit.microseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of microseconds (10⁻⁶ of a second).

### Query: `Cylindrical Rod Figure Readouts`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Satisfies End Face Snell Law`
- `Sat.Valuation.satisfies_fmla` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation. A formula is satisfied if all clauses in it are satisfied.
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...
- `FirstOrder.Language.Theory.models_iff_not_satisfiable` | module `Mathlib.ModelTheory.Satisfiability` | package Mathlib | **Semantic Entailment and Satisfiability.** For a theory $T$ and a sentence $\phi$ in a first-order language, $T$ semantically entails $\phi$ if and only if the set of sentences $T \cup \{\neg \phi\}$ is unsatisfiable.

### Query: `wall Incidence Angle Radians`
- `Real.Angle.toReal_le_pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Upper Bound of the Real Representative of an Angle.** For any angle $\theta$, its representative in the interval $(-\pi, \pi]$ is always less than or equal to $\pi$.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `IncidenceAlgebra` | module `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra` | package Mathlib | The `𝕜`-incidence algebra over `α`.

### Query: `Meets Wall Total Internal Reflection Threshold`
- `ProbabilityTheory.Fernique.normThreshold` | module `Mathlib.Probability.Distributions.Fernique` | package Mathlib | A sequence of real thresholds that will be used to cut the space into annuli. Chosen such that for a rotation invariant measure, an application of lemma `measure_le_mul_measure_gt_le_of_map_rotation_eq_self` gives `μ...
- `Submodule.reflection` | module `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` | package Mathlib | Reflection in a complete subspace of an inner product space. The word "reflection" is sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes more generally to cover operation...
- `Module.reflection` | module `Mathlib.LinearAlgebra.Reflection` | package Mathlib | Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define the endomorphism of `M` for which `y ↦ y - (f y) • x`. It is an involutive endomorphism of `M` fixing the kernel of `f`...

### Query: `Can Be Guided By Total Internal Reflection`
- `CanLift` | module `Mathlib.Tactic.Lift` | package Mathlib | A class specifying that you can lift elements from `α` to `β` assuming `cond` is true. Used by the tactic `lift`.
- `CategoryTheory.OrthogonalReflection.corepresentableBy` | module `Mathlib.CategoryTheory.Presentable.OrthogonalReflection` | package Mathlib | The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` exhibits `reflectionObj W Z κ` as the image of `Z` by the left adjoint of the inclusion `W.isLocal.ι`.
- `ComplexShape.Embedding.instIsRelIffOp` | module `Mathlib.Algebra.Homology.Embedding.Basic` | package Mathlib | **Reflectivity of Opposite Embeddings.** If an embedding of complex shapes is reflective, meaning it preserves the relation between indices in both directions, then its opposite embedding is also reflective.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Set.Ioi` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PiNat.cylinder` (Mathlib)
- `MeasureTheory.squareCylinders` (Mathlib)
- `LengthUnit.micrometers` (PhysLean)
- `hyperoperation_two` (Mathlib)
- `TimeUnit.microseconds` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `εNFA.IsPath` (Mathlib)
- `Sat.Valuation.satisfies_fmla` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)
- `FirstOrder.Language.Theory.models_iff_not_satisfiable` (Mathlib)
- `Real.Angle.toReal_le_pi` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `IncidenceAlgebra` (Mathlib)
- `ProbabilityTheory.Fernique.normThreshold` (Mathlib)
- `Submodule.reflection` (Mathlib)
- `Module.reflection` (Mathlib)
- `CanLift` (Mathlib)
- `CategoryTheory.OrthogonalReflection.corepresentableBy` (Mathlib)
- `ComplexShape.Embedding.instIsRelIffOp` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0010.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.CanBeGuidedByTotalInternalReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.CylindricalRodFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.CylindricalRodSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.IsMaximumGuidedAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.MeetsWallTotalInternalReflectionThreshold`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.OpticalRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0010.SatisfiesEndFaceSnellLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

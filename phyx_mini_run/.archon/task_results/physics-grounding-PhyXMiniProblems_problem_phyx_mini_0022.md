# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0022.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0022.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Pfund Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PMF.monad_map_eq_map` | module `Mathlib.Probability.ProbabilityMassFunction.Constructions` | package Mathlib | **Equivalence of Functorial Map and PMF Map.** For any function $f : \alpha \to \beta$ and any probability mass function $p$ on $\alpha$, the application of the functorial map operator $f <\$> p$ is equal to the push-...
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.

### Query: `Slab Face`
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.SimplicialObject.δ` | module `Mathlib.AlgebraicTopology.SimplicialObject.Basic` | package Mathlib | Face maps for a simplicial object.
- `Geometry.SimplicialComplex.not_facet_iff_subface` | module `Mathlib.Analysis.Convex.SimplicialComplex.Basic` | package Mathlib | **Characterization of Non-Facet Faces.** For any face $s$ of a simplicial complex $K$, $s$ is not a facet if and only if it is a proper subset of some other face $t$ in $K$.

### Query: `Pfund Point Label`
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.

### Query: `Pfund Ray Label`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `RayVector` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that `RayVector.Setoid` can be an instance.
- `ProbabilityTheory.paretoPDF` | module `Mathlib.Probability.Distributions.Pareto` | package Mathlib | The pdf of the Pareto distribution, as a function valued in `ℝ≥0∞`.

### Query: `Clear Surface Behavior`
- `Mathlib.Tactic.clear!` | module `Mathlib.Tactic.ClearExclamation` | package Mathlib | A variant of `clear` which clears not only the given hypotheses but also any other hypotheses depending on them
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Turing.PartrecToTM2.Λ'.clear` | module `Mathlib.Computability.TuringMachine.ToPartrec` | package Mathlib | **Conditional Stack Clearing.** The instruction `clear` takes a predicate $p$ on the stack alphabet, a stack identifier $k$, and a successor program position $q$. It represents the operation of clearing the contents o...

### Query: `Figure Point Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `PMF.monad_map_eq_map` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.SimplicialObject.δ` (Mathlib)
- `Geometry.SimplicialComplex.not_facet_iff_subface` (Mathlib)
- `OnePoint` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `SameRay` (Mathlib)
- `RayVector` (Mathlib)
- `ProbabilityTheory.paretoPDF` (Mathlib)
- `Mathlib.Tactic.clear!` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Turing.PartrecToTM2.Λ'.clear` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0022.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.ClearSurfaceBehavior`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.FigurePointCentimeters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.MatchesAnswerToNearestHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.MatchesPfundFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.PfundExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.PfundFigureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.PfundMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.PfundPointLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.PfundRayLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.SatisfiesCriticalRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.SatisfiesPfundCriticalAngleLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0022.SlabFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

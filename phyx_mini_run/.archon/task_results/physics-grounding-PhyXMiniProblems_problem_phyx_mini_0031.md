# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0031.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0031.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7a49c9ef1b82edde565f4993571723c7fde99bb61fb34c0cf8ccb79d0204f7d4
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

### Query: `Thin Lens`
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` | module `Mathlib.CategoryTheory.FinCategory.Basic` | package Mathlib | **Finite Category Instance for Thin Categories. Let $J$ be a small category that is thin (meaning there is at most one morphism between any two objects). If the set of objects in $J$ is finite, then $J$ is a finite ca...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Two Lens Setup`
- `CategoryTheory.Limits.BinaryFan.snd` | module `Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts` | package Mathlib | The second projection of a binary fan.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `CategoryTheory.Limits.PullbackCone.snd` | module `Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone` | package Mathlib | The second projection of a pullback cone.

### Query: `Has Stated Readouts`
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `HasAdjoint.adjoint` | module `Physlib.Mathematics.InnerProductSpace.Adjoint` | package PhysLean | **Uniqueness of the Adjoint Operator.** If a map $f: E \to F$ between inner product spaces over a field $\mathbb{k}$ has an adjoint $f'$, then the formally defined adjoint operator $f^*$ is equal to $f'$.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `Has Physical Axial Placement`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `CanonicalEnsemble.physicalProbability_def` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | **Definition of Physical Probability Density.** In a canonical ensemble, the physical probability density of a microstate $i$ at temperature $T$ is defined as the product of the mathematical probability density and th...

### Query: `Satisfies Two Lens Axial Geometry`
- `EuclideanGeometry.Sphere.secondInter_map` | module `Mathlib.Geometry.Euclidean.Sphere.SecondInter` | package Mathlib | **Invariance of the Second Intersection of a Sphere under Affine Isometries.** Let $s$ be a sphere in a Euclidean space $P$ with center $c$ and radius $r$, and let $f: P \to P_2$ be an affine isometry. For any point $...
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...

### Query: `Satisfies Thin Lens Equation`
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols` | package PhysLean | Those solutions which do not satisfy the condition `lineEqPropSol`.
- `Sat.Valuation.satisfies_fmla` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation. A formula is satisfied if all clauses in it are satisfied.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Satisfies Both Thin Lens Equations`
- `CategoryTheory.ThinSkeleton.equiv_of_both_ways` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | **Equivalence of Objects in a Thin Category.** In a thin category, two objects $X$ and $Y$ are isomorphic (and thus equivalent in the skeleton) if there exists a morphism from $X$ to $Y$ and a morphism from $Y$ to $X$.
- `RigidBody.euler_equations` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | When motion is described in body-fixed principal axes (I₁, I₂, I₃ diagonal), the equations of rotational motion (Euler’s equations) are: I₁ dω₁/dt + (I₃ − I₂) ω₂ ω₃ = M₁, with cyclic permutations. M is the external to...
- `MSSMACC.AnomalyFreePerp.InLineEqSol` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols` | package PhysLean | Those solutions which satisfy the condition `lineEqPropSol` but not `inQuadSolProp`.

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
- `CategoryTheory.instFinCategoryOfFintypeOfIsThin` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.Limits.BinaryFan.snd` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.Limits.PullbackCone.snd` (Mathlib)
- `HasSum` (Mathlib)
- `HasAdjoint.adjoint` (PhysLean)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `CanonicalEnsemble.physicalProbability_def` (PhysLean)
- `EuclideanGeometry.Sphere.secondInter_map` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` (PhysLean)
- `Sat.Valuation.satisfies_fmla` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `CategoryTheory.ThinSkeleton.equiv_of_both_ways` (Mathlib)
- `RigidBody.euler_equations` (PhysLean)
- `MSSMACC.AnomalyFreePerp.InLineEqSol` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0031.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.HasPhysicalAxialPlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.HasStatedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.MatchesAnswerToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.SatisfiesBothThinLensEquations`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.SatisfiesThinLensEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.SatisfiesTwoLensAxialGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.ThinLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0031.TwoLensSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

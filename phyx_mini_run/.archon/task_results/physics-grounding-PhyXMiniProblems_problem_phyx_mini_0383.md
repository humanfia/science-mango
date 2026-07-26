# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0383.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0383.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:b41ab81bdabcfa47c43613181c6e479140eb7f7a4f9dd2f6c1632ddf0ad52483
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Force Magnitude`
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.

### Query: `area In Square Meters`
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.

### Query: `area In Square Centimeters`
- `DimArea.squareFoot_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Conversion of square feet to SI units.** The area of one square foot is exactly $0.09290304$ square meters in the International System of Units.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `pressure In Pascals`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `pressure In Kilopascals`
- `DimPressure.bar` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 bar (100,000 pascals).
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `force In Newtons`
- `UnitExamples.NewtonsSecondWithDim` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `F = m a` using `WithDim` with `.val`.
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` | module `Physlib.Electromagnetism.Kinematics.FieldStrength` | package PhysLean | The field strength from an electromagnetic potential, as a tensor `F^{μν}`.
- `FluidDynamics.BodyForce` | module `Physlib.FluidDynamics.FluidState` | package PhysLean | A body-force field per unit mass on `d`-dimensional space.

### Query: `Supplied Valve Figure`
- `ValuativeRel.supp` | module `Mathlib.RingTheory.Valuation.ValuativeRel.Basic` | package Mathlib | The support of the valuation on `R`.
- `Valuation.restrict` | module `Mathlib.RingTheory.Valuation.Basic` | package Mathlib | The restriction of a valuation so that it takes values in its `valueGroup₀`.
- `Valuation.leSubmodule` | module `Mathlib.RingTheory.Valuation.Integers` | package Mathlib | The `v.integer`-submodule of `R` of elements whose valuation is less than or equal to a certain value.

### Query: `Valve Cylinder Setup`
- `MeasureTheory.cylinder` | module `Mathlib.MeasureTheory.Constructions.Cylinders` | package Mathlib | Given a finite set `s` of indices, a cylinder is the preimage of a set `S` of `∀ i : s, α i` by the projection from `∀ i, α i` to `∀ i : s, α i`.
- `SymbolicDynamics.FullShift.mulOccursInAt_eq_cylinder` | module `Mathlib.Dynamics.SymbolicDynamics.Basic` | package Mathlib | We call *occurrence set* for pattern `p` and position `g` the set of configurations in which a pattern `p` occurs at position `g`. This proves that it is exactly the cylinder corresponding to the pattern obtained by t...
- `PiNat.update_mem_cylinder` | module `Mathlib.Topology.MetricSpace.PiNat` | package Mathlib | **Cylinder Membership under Pointwise Update.** For any sequence $x$ in a product space $\prod_{i \in \mathbb{N}} E_i$, any natural number $n$, and any value $y \in E_n$, the sequence obtained by updating $x$ at index...

### Query: `Matches Supplied Valve Figure`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `SimpleGraph.Subgraph.IsMatching.support_eq_verts` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Support of a Matching.** For any subgraph $M$ of a simple graph, if $M$ is a matching, then the support of $M$ is equal to the set of its vertices.
- `SimpleGraph.Subgraph.IsMatching.iSup` | module `Mathlib.Combinatorics.SimpleGraph.Matching` | package Mathlib | **Matching of a Union of Subgraphs.** Let $\{H_i\}_{i \in I}$ be a family of subgraphs of a graph $G$. If each $H_i$ is a matching and the supports of the subgraphs are pairwise disjoint, then the supremum (union) of...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `FluidDynamics.BodyForce` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `DimArea.squareMeter` (PhysLean)
- `DimArea.squareFoot_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimArea.are` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)
- `DimPressure.bar` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure` (PhysLean)
- `UnitExamples.NewtonsSecondWithDim` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.toFieldStrength` (PhysLean)
- `FluidDynamics.BodyForce` (PhysLean)
- `ValuativeRel.supp` (Mathlib)
- `Valuation.restrict` (Mathlib)
- `Valuation.leSubmodule` (Mathlib)
- `MeasureTheory.cylinder` (Mathlib)
- `SymbolicDynamics.FullShift.mulOccursInAt_eq_cylinder` (Mathlib)
- `PiNat.update_mem_cylinder` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `SimpleGraph.Subgraph.IsMatching.support_eq_verts` (Mathlib)
- `SimpleGraph.Subgraph.IsMatching.iSup` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0383.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.ForceMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.HasPhysicalValveParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.IsUniqueClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.MatchesPressureOnlyOpeningModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.MatchesSuppliedValveFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.SatisfiesValvePressureForceLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.SuppliedValveFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0383.ValveCylinderSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

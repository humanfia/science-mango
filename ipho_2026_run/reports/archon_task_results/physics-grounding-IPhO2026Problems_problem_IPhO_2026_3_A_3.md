# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_3.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:eb117d7402e6db92fa0d2362f42a1fc2043b79145af62b987604640d35afa8e9
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `ScaleSeparation`
- `SeparationQuotient` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov quotient. This quotient is guaranteed to be a T₀ space.
- `ONote.scale` | module `Mathlib.SetTheory.Ordinal.Notation` | package Mathlib | `scale x o` is the ordinal notation for `ω ^ x * o`.
- `SetRel.isSeparated_insert` | module `Mathlib.Data.Rel.Separated` | package Mathlib | **Separation of an Augmented Set.** For a symmetric relation $R$, a set $s \cup \{x\}$ is separated with respect to $R$ if and only if $s$ is separated and every element $y \in s$ related to $x$ by $R$ is equal to $x$.

### Query: `ParamagneticToroid`
- `CategoryTheory.Tor'` | module `Mathlib.CategoryTheory.Monoidal.Tor` | package Mathlib | An alternative definition of `Tor`, where we left-derive in the first factor instead.
- `Module.IsTorsionFree` | module `Mathlib.Algebra.Module.Torsion.Free` | package Mathlib | An `R`-module `M` is torsion-free if scalar multiplication by an element `r : R` is injective if multiplication (on `R`) by `r` is. For domains, this is equivalent to the usual condition of `r • m = 0 → r = 0 ∨ m = 0`...
- `CategoryTheory.Tor'_map_app` | module `Mathlib.CategoryTheory.Monoidal.Tor` | package Mathlib | **The Tor Functor.** For a natural number $n$, the functor $\text{Tor}'_n$ is a bifunctor from $\mathcal{C} \times \mathcal{C}$ to $\mathcal{C}$ (represented as a functor from $\mathcal{C}$ to the category of functors...

### Query: `DenseInsulatedWinding`
- `Dense` | module `Mathlib.Topology.Defs.Basic` | package Mathlib | A set is dense in a topological space if every point belongs to its closure.
- `dense_liouville` | module `Mathlib.NumberTheory.Transcendental.Liouville.Residual` | package Mathlib | The set of Liouville numbers in dense.
- `dense_irrational` | module `Mathlib.Topology.Instances.Irrational` | package Mathlib | **Density of Irrational Numbers.** The set of irrational numbers is dense in the real numbers $\mathbb{R}$.

### Query: `UniformMagneticState`
- `UniformContinuous` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then `f x` is close to `f y` no matter whe...
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ElectromagneticPotential.magneticField` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The magnetic field from the electromagnetic potential.

### Query: `UniformMagneticIncrement`
- `UniformContinuous` | module `Mathlib.Topology.UniformSpace.Defs` | package Mathlib | A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then `f x` is close to `f y` no matter whe...
- `IsUniformInducing.isUltraUniformity` | module `Mathlib.Topology.UniformSpace.Ultra.Completion` | package Mathlib | **Inheritance of Ultra-Uniformity under Uniform Inducing Maps.** If $f: X \to Y$ is a uniform inducing map and $Y$ is an ultra-uniform space, then $X$ is also an ultra-uniform space.
- `SzemerediRegularity.increment` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Increment` | package Mathlib | The **increment partition** in Szemerédi's Regularity Lemma. If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition with a slightly higher energy. This is helpful since the...

### Query: `WorkIncrementReadouts`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SzemerediRegularity.increment` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Increment` | package Mathlib | The **increment partition** in Szemerédi's Regularity Lemma. If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition with a slightly higher energy. This is helpful since the...
- `SzemerediRegularity.energy_increment` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Increment` | package Mathlib | The increment partition has energy greater than the original one by a known fixed amount.

### Query: `SatisfiesWorkModel`
- `FirstOrder.Language.Theory.Model.isSatisfiable` | module `Mathlib.ModelTheory.Satisfiability` | package Mathlib | **Satisfiability of a Theory with a Model.** A first-order theory $T$ is satisfiable if there exists a nonempty structure $M$ that is a model of $T$.
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.
- `FirstOrder.Language.Theory.IsSatisfiable` | module `Mathlib.ModelTheory.Satisfiability` | package Mathlib | A theory is satisfiable if a structure models it.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Scale Separation`
- `SeparationQuotient` | module `Mathlib.Topology.Defs.Filter` | package Mathlib | The quotient of a topological space by its `inseparableSetoid`. Also called the Kolmogorov quotient. This quotient is guaranteed to be a T₀ space.
- `ONote.scale` | module `Mathlib.SetTheory.Ordinal.Notation` | package Mathlib | `scale x o` is the ordinal notation for `ω ^ x * o`.
- `Metric.AreSeparated` | module `Mathlib.Topology.MetricSpace.MetricSeparated` | package Mathlib | Two sets in an (extended) metric space are called *metric separated* if the (extended) distance between `x ∈ s` and `y ∈ t` is bounded from below by a positive constant.

### Query: `Paramagnetic Toroid`
- `CategoryTheory.Tor'` | module `Mathlib.CategoryTheory.Monoidal.Tor` | package Mathlib | An alternative definition of `Tor`, where we left-derive in the first factor instead.
- `Module.IsTorsionFree` | module `Mathlib.Algebra.Module.Torsion.Free` | package Mathlib | An `R`-module `M` is torsion-free if scalar multiplication by an element `r : R` is injective if multiplication (on `R`) by `r` is. For domains, this is equivalent to the usual condition of `r • m = 0 → r = 0 ∨ m = 0`...
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.

## Grounded Mathlib/PhysLean names

- `SeparationQuotient` (Mathlib)
- `ONote.scale` (Mathlib)
- `SetRel.isSeparated_insert` (Mathlib)
- `CategoryTheory.Tor'` (Mathlib)
- `Module.IsTorsionFree` (Mathlib)
- `CategoryTheory.Tor'_map_app` (Mathlib)
- `Dense` (Mathlib)
- `dense_liouville` (Mathlib)
- `dense_irrational` (Mathlib)
- `UniformContinuous` (Mathlib)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticField` (PhysLean)
- `UniformContinuous` (Mathlib)
- `IsUniformInducing.isUltraUniformity` (Mathlib)
- `SzemerediRegularity.increment` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `SzemerediRegularity.increment` (Mathlib)
- `SzemerediRegularity.energy_increment` (Mathlib)
- `FirstOrder.Language.Theory.Model.isSatisfiable` (Mathlib)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `FirstOrder.Language.Theory.IsSatisfiable` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `SeparationQuotient` (Mathlib)
- `ONote.scale` (Mathlib)
- `Metric.AreSeparated` (Mathlib)
- `CategoryTheory.Tor'` (Mathlib)
- `Module.IsTorsionFree` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_A_3.DenseInsulatedWinding`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.ParamagneticToroid`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.SatisfiesWorkModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.ScaleSeparation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.UniformMagneticIncrement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.UniformMagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_3.WorkIncrementReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

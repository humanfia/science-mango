# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_1_C_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:788e92d60a64376d49c1e22976f703bbcb80edb06971f1fb4f81f7c4d8bd8ef1
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `DimMass`
- `UnitExamples.EnergyMassWithDim'` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `E = m c^2` using `WithDim`.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.

### Query: `AngularFrequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.ω_pos` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator is positive.

### Query: `DimAction`
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `WithDim.instMulActionNNReal` | module `Physlib.Units.WithDim.Basic` | package PhysLean | **Scalar Action on Dimension-Tagged Types.** Given a physical dimension $d$ and a type $M$ equipped with a scalar action of the nonnegative real numbers $\mathbb{R}_{\ge 0}$, the type of elements of $M$ tagged with di...
- `instMulActionNNRealElemDimSet` | module `Physlib.Units.UnitDependent` | package PhysLean | **Action of Nonnegative Reals on Dimension-Consistent Subsets.** Given a multiplicative unit-dependent type $M$ equipped with an action of the nonnegative real numbers $\mathbb{R}_{\ge 0}$, there is a natural action o...

### Query: `atomicMassUnit`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit.ounces` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The mass unit of (avoirdupois) ounces (0.028 349 523 125 of a kilogram).

### Query: `reducedPlanckConstant`
- `IsReduced` | module `Mathlib.Algebra.GroupWithZero.Basic` | package Mathlib | A structure that has zero and pow is reduced if it has no nonzero nilpotent elements.
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `Constants.ℏ` | module `Physlib.QuantumMechanics.PlanckConstant` | package PhysLean | The value of the reduced Planck's constant in units of J.s.

### Query: `scalarInUnits`
- `Units` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | Units of a `Monoid`, bundled version. Notation: `αˣ`. An element of a `Monoid` is a unit if it has a two-sided inverse. This version bundles the inverse element so that it can be computed. For a predicate see `IsUnit`.
- `ConjAct.unitsScalar` | module `Mathlib.GroupTheory.GroupAction.ConjAct` | package Mathlib | **Conjugation Action of Units on a Monoid.** For a monoid $M$, the group of units $M^\times$ acts on $M$ via conjugation. Specifically, for any unit $g \in M^\times$ and any element $h \in M$, the action is defined by...
- `PUnit.smul_eq` | module `Mathlib.Algebra.Module.PUnit` | package Mathlib | **Scalar Action on the Unit Type.** For any scalar $r$ in a type $R$, the scalar multiplication of $r$ with the unique element of the unit type $PUnit$ always results in that same unique element.

### Query: `siScalar`
- `IsScalarTower` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | An instance of `IsScalarTower M N α` states that the multiplicative action of `M` on `α` is determined by the multiplicative actions of `M` on `N` and `N` on `α`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.

### Query: `momentumSquaredNorm`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `Complex.normSq` | module `Mathlib.Data.Complex.Basic` | package Mathlib | The norm squared function.
- `Quaternion.normSq_eq_norm_mul_self` | module `Mathlib.Analysis.Quaternion` | package Mathlib | **Squared Norm of a Quaternion.** For any quaternion $a$, the squared norm of $a$ is equal to the product of its norm with itself, i.e., $\text{normSq}(a) = \|a\|^2$.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `UnitExamples.EnergyMassWithDim'` (PhysLean)
- `dimH` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ω_pos` (PhysLean)
- `dimH` (Mathlib)
- `WithDim.instMulActionNNReal` (PhysLean)
- `instMulActionNNRealElemDimSet` (PhysLean)
- `MassUnit` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `MassUnit.ounces` (PhysLean)
- `IsReduced` (Mathlib)
- `LocallyConstant` (Mathlib)
- `Constants.ℏ` (PhysLean)
- `Units` (Mathlib)
- `ConjAct.unitsScalar` (Mathlib)
- `PUnit.smul_eq` (Mathlib)
- `IsScalarTower` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `UnitChoices.SI_mass` (PhysLean)
- `Momentum` (PhysLean)
- `Complex.normSq` (Mathlib)
- `Quaternion.normSq_eq_norm_mul_self` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_1_C_2.AngularFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.C2NumericalInputs`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.DimAction`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.DimMass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.DissociationAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.MakesAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.OzonePhotodissociationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.QuotedPreviousPartC1Result`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.RoundsTo`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_2.ValidOzonePhotodissociationPhysics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

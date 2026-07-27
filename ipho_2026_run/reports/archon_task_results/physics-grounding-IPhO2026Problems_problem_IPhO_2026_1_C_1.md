# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:89e62888cc487df5288a09d28537831b71ac76dcc8c1b1872d45b2b12df61ca2
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

### Query: `MassQuantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `ActionQuantity`
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `Action` | module `Mathlib.CategoryTheory.Action.Basic` | package Mathlib | An `Action V G` represents a bundled action of the monoid `G` on an object of some category `V`. As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`, while when `V = Type` this is a `G`-...
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `AngularFrequencyQuantity`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `MomentumQuantity2`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `QuantumMechanics.momentumCLM` | module `Physlib.QuantumMechanics.Operators.Momentum` | package PhysLean | Component `i` of the momentum operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`.

### Query: `scalarSI`
- `IsScalarTower` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | An instance of `IsScalarTower M N α` states that the multiplicative action of `M` on `α` is determined by the multiplicative actions of `M` on `N` and `N` on `α`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.

### Query: `speedSI`
- `DimSpeed.oneKnot_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of one knot in SI units.** In the International System of Units (SI), the value of one knot is exactly $\frac{463}{900}$ meters per second.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.

### Query: `momentumSI`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.

### Query: `dot2`
- `dotProduct` | module `Mathlib.Data.Matrix.Mul` | package Mathlib | `dotProduct v w` is the sum of the entrywise products `v i * w i`. See also `dotProductEquiv`.
- `Matrix.vec2_dotProduct'` | module `Mathlib.LinearAlgebra.Matrix.Notation` | package Mathlib | **Dot Product of 2-Vectors.** The dot product of two vectors in $\alpha^2$, represented as $[a_0, a_1]$ and $[b_0, b_1]$, is equal to the sum of the products of their corresponding components, $a_0 b_0 + a_1 b_1$.
- `Matrix.vec2_dotProduct` | module `Mathlib.LinearAlgebra.Matrix.Notation` | package Mathlib | **Dot Product of 2-Dimensional Vectors.** The dot product of two vectors $v, w \in \alpha^2$ is equal to the sum of the products of their components, specifically $v_0 w_0 + v_1 w_1$.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `MulAction` (Mathlib)
- `Action` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `Momentum` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `QuantumMechanics.momentumCLM` (PhysLean)
- `IsScalarTower` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `UnitChoices.SI_mass` (PhysLean)
- `DimSpeed.oneKnot_in_SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `Momentum` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `dotProduct` (Mathlib)
- `Matrix.vec2_dotProduct'` (Mathlib)
- `Matrix.vec2_dotProduct` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_1_C_1.ActionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.AngularFrequencyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.DissociationAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.IsMinimumDissociationFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.MomentumQuantity2`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.PhotodissociationParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_1_C_1.ValidPhotodissociationParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

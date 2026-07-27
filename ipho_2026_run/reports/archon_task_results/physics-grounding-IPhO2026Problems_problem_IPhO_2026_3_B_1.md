# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_1.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c10ffd0a6f9782d8bab4a08cfb3324c9ac89eac02c1a7b5485f01253738bdb9d
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `energyInJoules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).

### Query: `ParamagneticTorus`
- `torusIntegral` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `TorusIntegrable` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | A function `f : ℂⁿ → E` is integrable on the generalized torus if the function `f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`.

### Query: `ParamagneticTorusLaws`
- `torusIntegral` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`
- `TorusIntegrable` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | A function `f : ℂⁿ → E` is integrable on the generalized torus if the function `f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `Paramagnetic Torus`
- `torusMap` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The n-dimensional exponential map $θ_i ↦ c + R e^{θ_i*I}, θ ∈ ℝⁿ$ representing a torus in `ℂⁿ` with center `c ∈ ℂⁿ` and generalized radius `R ∈ ℝⁿ`, so we can adjust it to every n axis.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `torusIntegral` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`

### Query: `Paramagnetic Torus Laws`
- `torusIntegral` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Electromagnetism.ElectromagneticPotential.ofElectromagneticField_electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field of the electromagnetic potential created from the electric field `E` and the magnetic field `B` is `E`, as long as Gauss's law for magnetism and Faraday's law are satisfied.

### Query: `heat Transferred Into isothermal`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf` | module `Mathlib.GroupTheory.Focal` | package Mathlib | Isomorphism theorem: `G / ker(V) ≅ P / P*`.

## Grounded Mathlib/PhysLean names

- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.kilowattHour` (PhysLean)
- `torusIntegral` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `TorusIntegrable` (Mathlib)
- `torusIntegral` (Mathlib)
- `TorusIntegrable` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `torusMap` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `torusIntegral` (Mathlib)
- `torusIntegral` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.ofElectromagneticField_electricField` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_B_1.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_1.ParamagneticTorusLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

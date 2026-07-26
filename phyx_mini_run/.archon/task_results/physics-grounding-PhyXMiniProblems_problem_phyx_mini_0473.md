# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0473.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0473.tex`
- Grounding status: complete
- Search backend: local
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Fuel Mass Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit.quarters` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The mass unit of a quarter (28 pounds).

### Query: `Specific Combustion Energy Quantity`
- `UnitExamples.EnergyMass'` | module `Physlib.Units.Examples` | package PhysLean | The equation `E = m c^2`, in this version everything is written explicitly in terms of a choice of units.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Lean.Meta.DiscrTree.keysSpecific` | module `Mathlib.Lean.Meta.DiscrTree` | package Mathlib | Check if a `keys : Array DiscTree.Key` is "specific", i.e. something other than `[*]` or `[=, *, *, *]`.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `fuel Mass In Grams`
- `MassUnit.grams` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The mass unit of grams (10^(-3) of a kilogram).
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.

### Query: `combustion Energy In Joules Per Gram`
- `UnitExamples.example1_energyMass` | module `Physlib.Units.Examples` | package PhysLean | **Energy-Mass Equivalence for Two Kilograms.** In the International System of Units (SI), a mass of $2\text{ kg}$ corresponds to an energy of $2 \times 299,792,458^2\text{ joules}$, consistent with the mass-energy equ...
- `TwoHiggsDoublet.gramVector` | module `Physlib.Particles.BeyondTheStandardModel.TwoHDM.GramMatrix` | package PhysLean | A real vector containing the components of the Gram matrix in the Pauli basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Figure Arrow Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Quiver.Hom.toPos` | module `Mathlib.Combinatorics.Quiver.Symmetric` | package Mathlib | Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V`

### Query: `Figure Temperature Label`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `TemperatureUnit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The choices of translationally-invariant metrics on the temperature-manifold. Such a choice corresponds to a choice of units for temperature.

### Query: `Figure Energy Label`
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.
- `Hamming` | module `Mathlib.InformationTheory.Hamming` | package Mathlib | Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the sup norm.
- `Finpartition.coe_energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | **Energy of a Partition.** For a simple graph $G$ and a finite partition $\mathcal{P}$ of its vertex set, the energy of $\mathcal{P}$ (viewed as an element of a strictly ordered field) is equal to the sum of the squar...

### Query: `Supplied Heat Engine Figure`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `MassUnit.quarters` (PhysLean)
- `UnitExamples.EnergyMass'` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Lean.Meta.DiscrTree.keysSpecific` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `MassUnit.grams` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `MassUnit` (PhysLean)
- `UnitExamples.example1_energyMass` (PhysLean)
- `TwoHiggsDoublet.gramVector` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Quiver.Hom.toPos` (Mathlib)
- `Temperature` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `TemperatureUnit` (PhysLean)
- `Finpartition.energy` (Mathlib)
- `Hamming` (Mathlib)
- `Finpartition.coe_energy` (Mathlib)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0473.FigureArrowDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.FigureEnergyLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.FigureTemperatureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.FuelMassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.GasolineTruckEngineCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.MatchesProblemStatementAndPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.ObeysGasolineHeatEngineCycleLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.SpecificCombustionEnergyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0473.SuppliedHeatEngineFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

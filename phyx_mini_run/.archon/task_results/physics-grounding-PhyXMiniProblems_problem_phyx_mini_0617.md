# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0617.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0617.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:261a46317b6457729d2cee58a70c47a45f544ee138503aa713d380cdf5b86145
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

### Query: `Mass Quantity`
- `MassUnit` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The choices of translationally-invariant metrics on the mass-manifold. Such a choice corresponds to a choice of units for mass.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.

### Query: `action Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `WithDim.instMulActionNNReal` | module `Physlib.Units.WithDim.Basic` | package PhysLean | **Scalar Action on Dimension-Tagged Types.** Given a physical dimension $d$ and a type $M$ equipped with a scalar action of the nonnegative real numbers $\mathbb{R}_{\ge 0}$, the type of elements of $M$ tagged with di...

### Query: `Action Quantity`
- `MulAction` | module `Mathlib.Algebra.Group.Action.Defs` | package Mathlib | Type class for monoid actions on types, with notation `g • p`. The `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`. More precisely this means that the action satisfies the two ax...
- `Action` | module `Mathlib.CategoryTheory.Action.Basic` | package Mathlib | An `Action V G` represents a bundled action of the monoid `G` on an object of some category `V`. As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`, while when `V = Type` this is a `G`-...
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `Wave Number Quantity`
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | The wavenumbers associated with the energy eigenstates. This corresponds to the set `2 π / (a N) * (n - ⌊N/2⌋)` for `n : Fin T.N`. It is defined as such so it sits in the Brillouin zone.
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Exponential Property of the Quanta Wave Number.** For any site index $n \in \{0, \dots, N-1\}$ and any quanta wave number $k$, the complex exponential of $i \cdot k \cdot (n+1) \cdot a$ is equal to the product of th...
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` | module `Physlib.CondensedMatter.TightBindingChain.Basic` | package PhysLean | **Quantized Wave Number Periodic Identity.** For any natural number $n$ and any quantized wave number $k$ associated with a tight-binding chain of $N$ sites and lattice constant $a$, the complex exponential $\exp(i k...

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `mass In Kilograms`
- `MassUnit.kilograms` | module `Physlib.ClassicalMechanics.Mass.MassUnit` | package PhysLean | The definition of a mass unit of kilograms.
- `Finset.centerMass` | module `Mathlib.Analysis.Convex.Combination` | package Mathlib | Center of mass of a finite collection of points with prescribed weights. Note that we require neither `0 ≤ w i` nor `∑ w = 1`.
- `UnitChoices.SI_mass` | module `Physlib.Units.Basic` | package PhysLean | **SI Unit of Mass.** In the International System of Units (SI), the base unit of mass is defined to be the kilogram.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `action In Joule Seconds`
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.
- `DimEnergy.kilowattHour` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 kilowatt-hours, (3,600,000 J).
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `MassUnit` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finset.centerMass` (Mathlib)
- `Dimension` (PhysLean)
- `MulAction` (Mathlib)
- `WithDim.instMulActionNNReal` (PhysLean)
- `MulAction` (Mathlib)
- `Action` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `CondensedMatter.TightBindingChain.QuantaWaveNumber` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one` (PhysLean)
- `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `MassUnit.kilograms` (PhysLean)
- `Finset.centerMass` (Mathlib)
- `UnitChoices.SI_mass` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.kilowattHour` (PhysLean)
- `TimeUnit.seconds` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0617.ActionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.FigureLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.FinitePotentialWellSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.HasPhysicalPotentialWellParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.MatchesPotentialWellScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.MatchesSuppliedPotentialWellFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.PotentialValue`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.SatisfiesExteriorStationarySchrodingerEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.SatisfiesFiniteBoundaryConditionAtInfinity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.SuppliedPotentialWellFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.UsesStandardReducedPlanckConstant`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0617.WaveNumberQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

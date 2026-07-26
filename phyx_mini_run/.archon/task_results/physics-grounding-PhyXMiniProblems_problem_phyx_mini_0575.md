# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0575.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0575.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e94352ceb285f8db59496218fc2ef9f5473b3c4e65b18cd2e9641e7e3cc23be8
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `temperature In Kelvins`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `boltzmann Constant In Electron Volts Per Kelvin`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `TemperatureUnit.kelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The definition of a temperature unit of kelvin.
- `Constants.kBAx` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in units of `m ^ 2 kg s ^ (-2) K ^ (-1)`. As long as one does not use the underlying value of this quantity, then it can be used as Boltzmann's constant in an arbitrary set of units.

### Query: `fermi Dirac Occupation Probability`
- `MeasureTheory.Measure.dirac` | module `Mathlib.MeasureTheory.Measure.Dirac` | package Mathlib | The dirac measure.
- `ProbabilityTheory.mgf_dirac` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | **Moment Generating Function of a Dirac Distribution.** If a real-valued random variable $X$ has a distribution equal to the Dirac measure at $x \in \mathbb{R}$ under a measure $\mu$, then its moment generating functi...
- `PMF.pure_apply_self` | module `Mathlib.Probability.ProbabilityMassFunction.Monad` | package Mathlib | **Probability of a Dirac Delta at its Center.** For any element $a$, the probability mass function concentrated at $a$ assigns a probability of $1$ to the element $a$ itself.

### Query: `Semiconductor Material`
- `FluidDynamics.NavierStokes.materialAcceleration` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The material acceleration `∂ₜ u + (u · ∇)u`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Subsemiring.coe_matrix` | module `Mathlib.Data.Matrix.Basic` | package Mathlib | **Subsemiring of Matrices.** For any subsemiring $S$ of a semiring $R$, the set of $n \times n$ matrices whose entries all belong to $S$ forms a subsemiring of the semiring of $n \times n$ matrices over $R$.

### Query: `Dopant Kind`
- `Lean.Meta.RefinedDiscrTree.Key.forall` | module `Mathlib.Lean.Meta.RefinedDiscrTree.Basic` | package Mathlib | A dependent arrow.
- `Mathlib.Notation3.foldKind` | module `Mathlib.Util.Notation3` | package Mathlib | Keywording indicating whether to use a left- or right-fold.
- `Mathlib.Notation3.DelabKey.other` | module `Mathlib.Util.Notation3` | package Mathlib | **Generic Delaborator Key.** A delaborator key variant that identifies a delaborator using an arbitrary hierarchical name.

### Query: `Energy Reference`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `Diagram Feature`
- `YoungDiagram` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell is a cell in row `i` and colum...
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Display the string diagram for a given term. Example usage: ``` /- String diagram for the equality theorem. -/ #string_diagram MonoidalCategory.whisker_exchange /- String diagram for the morphism. -/ variable {C : Typ...
- `CategoryTheory.GlueData.diagram` | module `Mathlib.CategoryTheory.GlueData` | package Mathlib | (Implementation) The diagram to take colimit of.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `Temperature` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `LocallyConstant` (Mathlib)
- `TemperatureUnit.kelvin` (PhysLean)
- `Constants.kBAx` (PhysLean)
- `MeasureTheory.Measure.dirac` (Mathlib)
- `ProbabilityTheory.mgf_dirac` (Mathlib)
- `PMF.pure_apply_self` (Mathlib)
- `FluidDynamics.NavierStokes.materialAcceleration` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Subsemiring.coe_matrix` (Mathlib)
- `Lean.Meta.RefinedDiscrTree.Key.forall` (Mathlib)
- `Mathlib.Notation3.foldKind` (Mathlib)
- `Mathlib.Notation3.DelabKey.other` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `DimEnergy` (PhysLean)
- `Finpartition.energy` (Mathlib)
- `YoungDiagram` (Mathlib)
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` (Mathlib)
- `CategoryTheory.GlueData.diagram` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0575.AgreesWithinOneThousandth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.DiagramFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.DiagramMarkStyle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.DonorDopedSemiconductorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.DopantKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.EnergyReference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.HasPhysicalSemiconductorParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.IsNearBandGapMidpointWithin`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.IsUniqueNearestDisplayedProbability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.MatchesDonorDopedSiliconScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.MatchesProblemEnergyReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.MatchesSuppliedSemiconductorEnergyDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.SatisfiesFermiDiracOccupationLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.SemiconductorEnergyDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0575.SemiconductorMaterial`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

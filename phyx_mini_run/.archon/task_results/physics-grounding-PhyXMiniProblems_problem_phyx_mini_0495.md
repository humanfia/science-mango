# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0495.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0495.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:5ef63536d70526f91bc70550f83887481006905fe5c7951883497ea5ed7774f3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Volume Quantity`
- `Real.volume_real_Ico` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Volume of a Left-Closed, Right-Open Real Interval.** For any two real numbers $a$ and $b$, the real-valued volume of the interval $[a, b)$ is equal to the maximum of $b - a$ and $0$.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `Amount Of Substance Scale`
- `Polynomial.scaleRoots` | module `Mathlib.RingTheory.Polynomial.ScaleRoots` | package Mathlib | `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`.
- `Dimensionful.of_scaleUnit` | module `Physlib.Units.UnitDependent` | package PhysLean | **Scaling Property of Dimensionful Quantities.** For any dimensionful quantity $c$ associated with a type $M$ that carries a dimension, the value of $c$ at a scaled unit (formed by scaling a unit $u$ by the relative s...
- `ONote.scale` | module `Mathlib.SetTheory.Ordinal.Notation` | package Mathlib | `scale x o` is the ordinal notation for `ω ^ x * o`.

### Query: `Molar Thermal Coefficient Scale`
- `Polynomial.scaleRoots` | module `Mathlib.RingTheory.Polynomial.ScaleRoots` | package Mathlib | `scaleRoots p s` is a polynomial with root `r * s` for each root `r` of `p`.
- `ordinaryHypergeometricCoefficient` | module `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` | package Mathlib | The coefficients in the ordinary hypergeometric sum.
- `TemperatureUnit.val_pos` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | **Positivity of Temperature Unit Scales.** For any temperature unit, the real number representing its underlying scale is strictly positive.

### Query: `pressure In Pascals`
- `padicValNat` | module `Mathlib.Data.Nat.MaxPowDiv` | package Mathlib | For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`.
- `DimPressure.pascal` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 pascal, Pa.
- `DimPressure` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | Pressure as a dimensional quantity with dimension `ML⁻¹T⁻2`..

### Query: `volume In Cubic Metres`
- `Cubic.toPoly` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | Convert a cubic polynomial to a polynomial.
- `Space.volume_metricBall_three_real` | module `Physlib.SpaceAndTime.Space.Integrals.Basic` | package PhysLean | **Volume of the Unit Ball in Three-Dimensional Space.** The volume of the unit metric ball centered at the origin in $\mathbb{R}^3$ is equal to $\frac{4}{3}\pi$.
- `PureU1.Even.LineInCubic` | module `Physlib.QFT.QED.AnomalyCancellation.Even.LineInCubic` | package PhysLean | A property on `LinSols`, satisfied if every point on the line between the two planes in the basis through that point is in the cubic.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `temperature In Kelvins`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `Process Point`
- `MeasureTheory.stoppedProcess` | module `Mathlib.Probability.Process.Stopping` | package Mathlib | Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if `i ≤ τ ω`, and `u (τ ω) ω` otherwise. Intuitively, the stopped process stops evolving once the stopping time has occurred.
- `MeasureTheory.IsProgressive.div` | module `Mathlib.Probability.Process.Adapted` | package Mathlib | **Quotient of Progressive Processes.** If $u$ and $v$ are progressive processes taking values in a group $\beta$ with a measurable division operation, then their pointwise quotient $u/v$ (defined by $(u/v)_i(\omega) =...
- `MeasureTheory.IsStronglyProgressive.mul` | module `Mathlib.Probability.Process.Adapted` | package Mathlib | **Pointwise Product of Strongly Progressive Processes.** If $u$ and $v$ are strongly progressive stochastic processes and the state space is equipped with a continuous multiplication, then their pointwise product, def...

### Query: `Process BStep`
- `MeasureTheory.stoppedProcess` | module `Mathlib.Probability.Process.Stopping` | package Mathlib | Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if `i ≤ τ ω`, and `u (τ ω) ω` otherwise. Intuitively, the stopped process stops evolving once the stopping time has occurred.
- `Mathlib.Meta.FunProp.increaseSteps` | module `Mathlib.Tactic.FunProp.Types` | package Mathlib | Increase heartbeat, throws error when `maxSteps` was reached
- `Computation.Corec.f` | module `Mathlib.Data.Seq.Computation` | package Mathlib | Corecursor constructor for `corec`

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Real.volume_real_Ico` (Mathlib)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `Polynomial.scaleRoots` (Mathlib)
- `Dimensionful.of_scaleUnit` (PhysLean)
- `ONote.scale` (Mathlib)
- `Polynomial.scaleRoots` (Mathlib)
- `ordinaryHypergeometricCoefficient` (Mathlib)
- `TemperatureUnit.val_pos` (PhysLean)
- `padicValNat` (Mathlib)
- `DimPressure.pascal` (PhysLean)
- `DimPressure` (PhysLean)
- `Cubic.toPoly` (Mathlib)
- `Space.volume_metricBall_three_real` (PhysLean)
- `PureU1.Even.LineInCubic` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `Temperature` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `MeasureTheory.stoppedProcess` (Mathlib)
- `MeasureTheory.IsProgressive.div` (Mathlib)
- `MeasureTheory.IsStronglyProgressive.mul` (Mathlib)
- `MeasureTheory.stoppedProcess` (Mathlib)
- `Mathlib.Meta.FunProp.increaseSteps` (Mathlib)
- `Computation.Corec.f` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0495.AmountOfSubstanceScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.AxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.AxisUnit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.DiagramAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.EquilibriumGasState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.GasModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.HasPhysicalGasParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.IdealGasProcessSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.MatchesDisplayedInternalEnergyChange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.MatchesMonatomicIdealGasScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.MatchesProblemStatementReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.MatchesSuppliedPVDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.MolarThermalCoefficientScale`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.PressureVolumeDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.ProcessBStep`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.ProcessName`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.ProcessPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.RoundsToNearestTenJoules`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.SatisfiesMonatomicIdealGasLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0495.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

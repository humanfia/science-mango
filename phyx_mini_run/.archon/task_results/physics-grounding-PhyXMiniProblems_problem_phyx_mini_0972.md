# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0972.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0972.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e370d9fac20366e4cce2e0d58318a6c38936f321349fdfaaf37be6b9e6fef267
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `magnetic Flux Density Dimension`
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The magnetic field written as the curl of the vector potential as `∇ ⨯ A`.

### Query: `potential Difference Dimension`
- `Electromagnetism.ElectromagneticPotential.instSub` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Subtraction of Electromagnetic Potentials.** For a given dimension $d$, the difference between two electromagnetic potentials $A$ and $B$ is defined pointwise, such that $(A - B)(x) = A(x) - B(x)$ for all $x$.
- `Electromagnetism.ElectromagneticPotential.vectorPotential` | module `Physlib.Electromagnetism.Kinematics.VectorPotential` | package PhysLean | The vector potential from the electromagnetic potential.
- `QuantumMechanics.OneDimension.ReflectionlessPotential.reflectionlessPotential` | module `Physlib.QuantumMechanics.ReflectionlessPotential.Basic` | package PhysLean | Define the reflectionless potential as V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) -

### Query: `Length Magnitude Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.

### Query: `Speed Magnitude Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SpeedOfLight.val_pos` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | **Positivity of the Speed of Light.** The real-valued magnitude of the speed of light is strictly positive.

### Query: `Magnetic Flux Density Magnitude Quantity`
- `MeasureTheory.Measure.withDensity` | module `Mathlib.MeasureTheory.Measure.WithDensity` | package Mathlib | Given a measure `μ : Measure α` and a function `f : α → ℝ≥0∞`, `μ.withDensity f` is the measure such that for a measurable set `s` we have `μ.withDensity f s = ∫⁻ a in s, f a ∂μ`.
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `FluidDynamics.NavierStokes.momentumFlux` | module `Physlib.FluidDynamics.NavierStokes.Momentum` | package PhysLean | The convective momentum flux `rho u ⊗ u`.

### Query: `Potential Difference Magnitude Quantity`
- `Electromagnetism.ElectromagneticPotential.sub_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Subtraction of Electromagnetic Potentials.** The value of the difference between two electromagnetic potentials is equal to the difference of their individual values.
- `Electromagnetism.ElectromagneticPotential.vectorPotential` | module `Physlib.Electromagnetism.Kinematics.VectorPotential` | package PhysLean | The vector potential from the electromagnetic potential.
- `CovariantDerivative.difference` | module `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic` | package Mathlib | The difference of two covariant derivatives, as a one-form taking values in the endomorphisms of `V`.

### Query: `coherent SIReadout`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.coherentTopology` | module `Mathlib.CategoryTheory.Sites.Coherent.Basic` | package Mathlib | The coherent Grothendieck topology on a precoherent category `C`.
- `Mathlib.Tactic.Coherence.coherence_loop` | module `Mathlib.Tactic.CategoryTheory.Coherence` | package Mathlib | **Alias** of `Mathlib.Tactic.Coherence.coherenceLoop`. --- The main part of `coherence` tactic.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.MagneticField` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `Electromagnetism.ThreeDimension.magneticField_eq_3D` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.instSub` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.vectorPotential` (PhysLean)
- `QuantumMechanics.OneDimension.ReflectionlessPotential.reflectionlessPotential` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `List.Vector.length` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `SpeedOfLight.val_pos` (PhysLean)
- `MeasureTheory.Measure.withDensity` (Mathlib)
- `Electromagnetism.MagneticField` (PhysLean)
- `FluidDynamics.NavierStokes.momentumFlux` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.sub_val` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.vectorPotential` (PhysLean)
- `CovariantDerivative.difference` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.coherentTopology` (Mathlib)
- `Mathlib.Tactic.Coherence.coherence_loop` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0972.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.BloodFlowIdealization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.BloodVesselFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.BloodVesselMotionalEmfSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.ChargeSign`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.ConductingBlood`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.HasGivenBloodVesselMeasurements`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.IsClosestDisplayedFieldStrength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.LengthMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.MagneticFieldGlyph`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.MagneticFluxDensityMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.MatchesSuppliedBloodVesselFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.MatchesWrittenBloodVesselScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.PageNormalDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.PlanarAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.PlanarDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.PotentialDifferenceMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.RelativeOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.SatisfiesPerpendicularMotionalEmfLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.SpeedMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0972.VesselElectricalModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0104.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0104.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c3518917224a600dafb56393a07a334f5c294169ced24ed466909f86b4c746b1
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ThreeDimension.electricField_eq_3D` | module `Physlib.Electromagnetism.ThreeDimension.Basic` | package PhysLean | The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`.

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Intensity`
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `PosNum.ofZNum'` | module `Mathlib.Data.Num.Basic` | package Mathlib | Converts a `ZNum` to `Option PosNum`, where it is `some` if the `ZNum` was positive and `none` otherwise.
- `Order.isIntent_iff` | module `Mathlib.Order.Concept` | package Mathlib | **Characterization of Intents.** For a binary relation $r$, a subset $t$ of the codomain is an intent if and only if it is equal to the upper polar of its lower polar with respect to $r$.

### Query: `Electric Field Amplitude`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field as a Component of the Field Strength Matrix.** For a given electromagnetic potential $A$ and speed of light $c$, the $i$-th component of the electric field $\mathbf{E}$ at time $t$ and position $x$ is...

### Query: `Optical Wave Number`
- `ClassicalMechanics.WaveVector` | module `Physlib.ClassicalMechanics.WaveEquation.HarmonicWave` | package PhysLean | The wavevector which indicates a direction and has magnitude `2π/λ`.
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | The electromagnetic potential for a Harmonic wave travelling in the `x`-direction with wave number `k`.
- `ONote.NF` | module `Mathlib.SetTheory.Ordinal.Notation` | package Mathlib | A normal form ordinal notation has the form `ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ⋯ + ω ^ aₖ * nₖ` where `a₁ > a₂ > ⋯ > aₖ` and all the `aᵢ` are also in normal form. We will essentially only be interested in normal form ordina...

### Query: `Optical Angular Frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `ClassicalMechanics.HarmonicOscillator.ω_pos` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator is positive.

### Query: `intensity In Watts Per Square Meter`
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.
- `IsSquare` | module `Mathlib.Algebra.Group.Even` | package Mathlib | An element `a` of a type `α` with multiplication satisfies `IsSquare a` if `a = r * r`, for some root `r : α`.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `amplitude In Volts Per Meter`
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.
- `Electromagnetism.ElectromagneticPotential.vectorPotential` | module `Physlib.Electromagnetism.Kinematics.VectorPotential` | package PhysLean | The vector potential from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX_vectorPotential_zero_eq_zero` | module `Physlib.Electromagnetism.Vacuum.HarmonicWave` | package PhysLean | **Vanishing of the First Component of the Vector Potential for a Harmonic Wave Propagating in the x-direction.** For a harmonic electromagnetic wave propagating in the $x$-direction in free space with wave number $k$,...

### Query: `wave Number In Inverse Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `Ring.inverse` | module `Mathlib.Algebra.GroupWithZero.Units.Basic` | package Mathlib | Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is invertible and to `0` otherwise. This definition is somewhat ad hoc, but one needs a fully (rather than partially) defined...
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ThreeDimension.electricField_eq_3D` (PhysLean)
- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `intervalIntegral` (Mathlib)
- `PosNum.ofZNum'` (Mathlib)
- `Order.isIntent_iff` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq_fieldStrengthMatrix` (PhysLean)
- `ClassicalMechanics.WaveVector` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX` (PhysLean)
- `ONote.NF` (Mathlib)
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `ClassicalMechanics.HarmonicOscillator.ω_pos` (PhysLean)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `IsSquare` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.vectorPotential` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.harmonicWaveX_vectorPotential_zero_eq_zero` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `Ring.inverse` (Mathlib)
- `LengthUnit.nanometers` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0104.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.BrewsterInterfaceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.CartesianAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.CoordinatePlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.ElectricFieldAmplitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.FigureAmplitudeLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.HasEllipticallyPolarizedTransmission`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.HasLinearlyPolarizedReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.HasQuadraturePolarization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.IsAcuteOpticalAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.IsAtPolarizingAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.IsNearestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.MatchesProblemAndFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.ObeysFresnelTransmission`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.ObeysSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.OpticalAngularFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.OpticalIntensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.OpticalWaveNumber`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.PolarizationComponent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0104.WaveKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

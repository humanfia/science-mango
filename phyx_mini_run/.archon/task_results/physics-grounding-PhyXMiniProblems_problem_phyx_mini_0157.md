# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0157.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0157.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e04fab27672ef08a963137006e694c9b21f298394bc9a25512a345a01027da20
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Gas Volume`
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `Orientation.volumeForm` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | The volume form on an oriented real inner product space, a nonvanishing top-dimensional alternating form uniquely defined by compatibility with the orientation and inner product structure.
- `NVEHamiltonian.V` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.Basic` | package PhysLean | Helper to get the volume in an N-V Hamiltonian

### Query: `Constant Volume Gas Bulb`
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `EuclideanSpace.volume_closedBall` | module `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls` | package Mathlib | **Volume of a Closed Ball in Euclidean Space.** In a Euclidean space $\mathbb{R}^n$ indexed by a finite set $\iota$ of cardinality $n$, the volume of a closed ball of radius $r$ centered at a point $x$ is given by $$V...

### Query: `Two Bulb Gas Thermometer`
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `TwoSidedIdeal` | module `Mathlib.RingTheory.TwoSidedIdeal.Basic` | package Mathlib | A two-sided ideal of a ring `R` is a subset of `R` that contains `0` and is closed under addition, negation, and absorbs multiplication on both sides.
- `Temperature.ext_iff` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | **Extensionality of Temperature.** Two temperature values are equal if and only if their underlying numerical values are equal.

### Query: `Has Physical Gas Thermometer Parameters`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.

### Query: `Satisfies Constant Volume Ideal Gas Thermometry`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `IdealGas.ZIntegrable` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | **Integrability of the Ideal Gas Partition Function.** For a system of $n$ particles in a volume $V > 0$ at an inverse temperature $\beta > 0$, the ideal gas Hamiltonian is $Z$-integrable. This means that the Boltzman...

### Query: `Has Gas Thermometer Calibration Data`
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `entropy` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Entropy of a monophase ideal gas: S(U,V,N) = N s0 + N R (c log(U/U0) + log(V/V0) - (c+1) log(N/N0)).

### Query: `unknown Temperature eq 348 kelvin`
- `TemperatureUnit.kelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The definition of a temperature unit of kelvin.
- `TemperatureUnit.nanokelvin` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees nanokelvin (10^(-9) kelvin).
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `IdealGas` (PhysLean)
- `Orientation.volumeForm` (Mathlib)
- `NVEHamiltonian.V` (PhysLean)
- `IdealGas` (PhysLean)
- `LocallyConstant` (Mathlib)
- `EuclideanSpace.volume_closedBall` (Mathlib)
- `IdealGas` (PhysLean)
- `TwoSidedIdeal` (Mathlib)
- `Temperature.ext_iff` (PhysLean)
- `IdealGas.ideal_gas_law` (PhysLean)
- `HasSum` (Mathlib)
- `IdealGas` (PhysLean)
- `IdealGas.ideal_gas_law` (PhysLean)
- `IdealGas` (PhysLean)
- `IdealGas.ZIntegrable` (PhysLean)
- `IdealGas.ideal_gas_law` (PhysLean)
- `IdealGas` (PhysLean)
- `entropy` (PhysLean)
- `TemperatureUnit.kelvin` (PhysLean)
- `TemperatureUnit.nanokelvin` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0157.ConstantVolumeGasBulb`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0157.GasVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0157.HasGasThermometerCalibrationData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0157.HasPhysicalGasThermometerParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0157.SatisfiesConstantVolumeIdealGasThermometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0157.TwoBulbGasThermometer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

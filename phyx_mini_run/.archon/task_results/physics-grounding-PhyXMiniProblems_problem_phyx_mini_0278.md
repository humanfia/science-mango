# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0278.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0278.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:8a23da3559c0999415423485589aad6f91ae958a578525bd5bd033a2a7e50e01
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `harmonic oscillator angular frequency`
- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The real frequency selected by the damping regime. In the underdamped regime this is the oscillation frequency. In the critically damped regime it is `0`. In the overdamped regime this is the real split rate between t...
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | The characteristic length `ξ` of the harmonic oscillator is defined as `√(ℏ /(m ω))`.
- `ClassicalMechanics.HarmonicOscillator.ω` | module `Physlib.ClassicalMechanics.HarmonicOscillator.Basic` | package PhysLean | The angular frequency of the classical harmonic oscillator, `ω`, is defined as `√(k/m)`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Moment Of Inertia Quantity`
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `RigidBody.solidSphere_inertiaTensor` | module `Physlib.ClassicalMechanics.RigidBody.SolidSphere` | package PhysLean | The moment of inertia tensor of a solid sphere through its center of mass is `2/5 m R^2 * I`.
- `ProbabilityTheory.moment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Moment of a real random variable, `μ[X ^ p]`.

### Query: `Torque Magnitude Quantity`
- `DimPressure.torr` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure).
- `Real.Angle.tan` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The tangent of a `Real.Angle`.
- `RigidBody.rigid_body_work_and_power` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | The power delivered to a rigid body by forces is P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω, where F_tot is total force, V the reference point velocity, and M the torque. Translational and rotational contributions separate.

### Query: `Torsion Constant Quantity`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `CovariantDerivative.torsion_self` | module `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion` | package Mathlib | **Torsion of a Tangent Vector with Itself.** For any tangent vector $X_0$ in the tangent space at a point $x$, the torsion tensor of a covariant derivative evaluated on the pair $(X_0, X_0)$ is zero.
- `Submodule.torsion'` | module `Mathlib.Algebra.Module.Torsion.Basic` | package Mathlib | The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some `a` in `S`.

### Query: `Signed Angular Velocity Quantity`
- `RigidBodyMotion.angularVelocity` | module `Physlib.ClassicalMechanics.RigidBody.AngularVelocity` | package PhysLean | The angular velocity *vector* `ω(t)` of a rigid body moving in three-dimensional space: the vector dual to the angular velocity tensor `Ω(t)` under the hat map, `ω = Ωᵛ`. It is the angular velocity `ω` in the Landau–L...
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `RigidBodyMotion.angularVelocityTensor` | module `Physlib.ClassicalMechanics.RigidBody.AngularVelocity` | package PhysLean | The angular velocity tensor `Ω(t) = Ṙ(t) R(t)ᵀ` of a rigid body in motion, where `R(t) = orientation t`. It is the antisymmetric tensor `Ω` in the Landau–Lifshitz decomposition `v = V + Ω × r` of the velocity of a poi...

### Query: `time In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit.hours_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Hours to Seconds.** The ratio of the time unit representing one hour to the time unit representing one second is equal to the non-negative real number $3600$.

### Query: `moment Of Inertia In Kilogram Meter Squared`
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.
- `Ideal.inertiaDeg` | module `Mathlib.RingTheory.RamificationInertia.Inertia` | package Mathlib | Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`. When `q` is not prime, we us...
- `RigidBody.solidSphere_inertiaTensor` | module `Physlib.ClassicalMechanics.RigidBody.SolidSphere` | package PhysLean | The moment of inertia tensor of a solid sphere through its center of mass is `2/5 m R^2 * I`.

### Query: `torque Magnitude In Newton Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `DimPressure.torr` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 torr (1/760 of standard atmosphere pressure).

## Grounded Mathlib/PhysLean names

- `ClassicalMechanics.DampedHarmonicOscillator.angularFrequency` (PhysLean)
- `QuantumMechanics.OneDimension.HarmonicOscillator.ξ` (PhysLean)
- `ClassicalMechanics.HarmonicOscillator.ω` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `RigidBody.solidSphere_inertiaTensor` (PhysLean)
- `ProbabilityTheory.moment` (Mathlib)
- `DimPressure.torr` (PhysLean)
- `Real.Angle.tan` (Mathlib)
- `RigidBody.rigid_body_work_and_power` (PhysLean)
- `LocallyConstant` (Mathlib)
- `CovariantDerivative.torsion_self` (Mathlib)
- `Submodule.torsion'` (Mathlib)
- `RigidBodyMotion.angularVelocity` (PhysLean)
- `Orientation.oangle` (Mathlib)
- `RigidBodyMotion.angularVelocityTensor` (PhysLean)
- `TimeUnit.seconds` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit.hours_div_seconds` (PhysLean)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `Ideal.inertiaDeg` (Mathlib)
- `RigidBody.solidSphere_inertiaTensor` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `JoinedIn` (Mathlib)
- `DimPressure.torr` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0278.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.ApparatusComponent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.AxisDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.CurveKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.FigureAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.GraphPanel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.HasPhysicalTorsionPendulumParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.MomentOfInertiaQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.SatisfiesIdealTorsionPendulumLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.SignedAngularVelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.SuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.TorqueMagnitudeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.TorsionConstantQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.TorsionPendulumApparatus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0278.TorsionPendulumSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.

# Deterministic Review Candidate Pack

Iteration: 001
Exact review target count: 28

Review only these targets. Direct Lean compilation was already run in
parallel by the orchestrator; use the recorded result instead of rerunning it.

## 1. `IPhO2026Problems/problem_IPhO_2026_1_A_1.lean`

- Compile status: passed
- Open sorries: 6
- Direct-check seconds: 11.599
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_A_1.md`

### Lean excerpt
```lean
/ √2`.
-/
lemma opening_area_readout
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry) :
    gate.geometry.openingArea.val =
      gate.geometry.sideLength.val ^ 2 / Real.sqrt 2 := by
  sorry

/--
At the limiting configuration, the zero contact and hinge torques reduce
static equilibrium to equality of the pressure and effective-weight torques.
-/
lemma critical_torque_balance
    (gate : HydrostaticGate)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate) :
    gate.pressureTorque.val = gate.effectiveWeightTorque.val := by
  sorry

/--
The hydrostatic and torque equations determine the cube side in terms of
the two densities and the level difference.
-/
lemma side_length_from_hydrostatic_balance
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate) :
    gate.geometry.sideLength.val =
      gate.waterDensity.val * gate.levelDifference.val /
        (Real.sqrt 2 * (gate.blockDensity.val - gate.waterDensity.val)) := by
  sorry

/--
For a block of density `3ρ₀`, the general critical-balance formula simplifies
to `a = Δh / (2√2)`.
-/
lemma side_length_for_triple_density
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate)
    (hDensity : gate.blockDensity.val = 3 * gate.waterDensity.val) :
    gate.geometry.sideLength.val =
      gate.levelDifference.val / (2 * Real.sqrt 2) := by
  sorry

/--
The exact value obtained from `Δh = 1.41 m` is within half of one hundredth
of `0.50 m`, so `0.50 m` is the correct two-decimal report.
-/
lemma stated_value_rounds_to_half_meter :
    |(1.41 : ℝ) / (2 * Real.sqrt 2) - 0.50| < 0.005 := by
  sorry

end HydrostaticGateA1

open HydrostaticGateA1

/--
IPhO 2026 T1-A1: the critical cube side is `Δh / (2√2)`. For the stated
`Δh = 1.41 m`, its exact SI readout rounds to the reported `0.50 m` at two
decimal places; the strict `0.005 m` error bound expresses that rounding and
is not an experimental-uncertainty assumption.
-/
theorem problem_IPhO_2026_1_A_1
    (gate : HydrostaticGate)
    (hFigure : MatchesFigure1a gate.geometry)
    (hLaws : ObeysHydrostaticLaws gate)
    (hCritical : AtMaximumPermissibleDifference gate)
    (hData : MatchesProblemData gate) :
    gate.geometry.sideLength.val =
        gate.levelDifference.val / (2 * Real.sqrt 2) ∧
      |gate.geometry.sideLength.val - 0.50| < 0.005 := by
  sorry

end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
by a fully submerged solid cube of side a
and density 3*rho\_0, where rho\_0 is the density of water.  The cube is hinged
frictionlessly at O and may rotate about an axis perpendicular to the figure.
The maximum permitted difference in water levels is Delta h = 1.41 m.  Use
Figure 1a on the source page for the exact geometry and lever arms.

Current subquestion:
Calculate the side length a that makes Delta h = 1.41 m the maximum permissible water-level difference.

\paragraph{Current subquestion.}
Calculate the side length a that makes Delta h = 1.41 m the maximum permissible water-level difference.

\paragraph{Recorded answer/context.}
a = Delta h/(2*sqrt(2)) = 0.50 m.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-1.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_A\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_1_A_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_A_1.lean.md`
```markdown
d forces, hinge reaction, contact force, and
  torques.
- The four proposition-valued interfaces expose only concrete equations,
  inequalities, and orientation equalities. They replace absent
  hydrostatic-gate APIs without weakening the physical model.

## Grounding gaps

- No Mathlib/Physlib declaration was found for a hinged hydrostatic gate,
  Archimedean buoyancy plus hydrostatic resultant force on this slot, or the
  critical vanishing-contact torque condition. The local law interfaces expose
  all equations needed by a later proof.
- Physlib's fluid-dynamics APIs describe continuum fields and Navier–Stokes
  momentum balance, not this rigid, homogeneous, static gate calculation.
- The `archon dag-query` executable was unavailable on this lane's `PATH`.
  This target has no previous-part dependencies, so no sibling declaration was
  imported or re-derived through the dependency graph.

## Redraft requests

- Add
  `\lean{IPhO2026Problems.problem_IPhO_2026_1_A_1}` to the blueprint target
  environment so deterministic marker synchronization can associate the
  compiling declaration with
  `thm:physics:IPhO_2026_1_A_1:target`.
- No physics-contract redraft is otherwise needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_A_1.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 2. `IPhO2026Problems/problem_IPhO_2026_1_B_1.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 12.102
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_B_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_1.md`

### Lean excerpt
```lean
alSeparation.val
  maximum_separation_positive : 0 < s.maximumSeparation.val
  equal_masses : s.positron.mass.val = s.electron.mass.val
  positron_charge :
    s.positron.charge.val = s.chargeMagnitude.val
  electron_charge :
    s.electron.charge.val = -s.chargeMagnitude.val
  coulomb_constant_definition :
    s.coulombConstant.val =
      1 / (4 * Real.pi * s.vacuumPermittivity.val)
  bohr_radius_definition :
    s.bohrRadius.val =
      4 * Real.pi * s.vacuumPermittivity.val *
          s.reducedPlanckConstant.val ^ 2 /
        (s.positron.mass.val * s.chargeMagnitude.val ^ 2)
  figure_center_of_mass :
    s.positron.position.val = -s.electron.position.val
  figure_antiparallel_velocities :
    s.positron.velocity.val = -s.electron.velocity.val
  figure_positron_velocity_perpendicular :
    inner ℝ
        (s.positron.position.val - s.electron.position.val)
        s.positron.velocity.val = 0
  figure_electron_velocity_perpendicular :
    inner ℝ
        (s.positron.position.val - s.electron.position.val)
        s.electron.velocity.val = 0
  figure_initial_separation :
    ‖s.positron.position.val - s.electron.position.val‖ =
      s.initialSeparation.val
  initial_separation_is_one_hundred_bohr_radii :
    s.initialSeparation.val = 100 * s.bohrRadius.val
  figure_positron_angular_momentum_magnitude :
    s.positron.angularMomentumMagnitude.val =
      s.positron.mass.val * (s.initialSeparation.val / 2) *
        ‖s.positron.velocity.val‖
  figure_electron_angular_momentum_magnitude :
    s.electron.angularMomentumMagnitude.val =
      s.electron.mass.val * (s.initialSeparation.val / 2) *
        ‖s.electron.velocity.val‖
  positron_angular_momentum :
    s.positron.angularMomentumMagnitude.val =
      s.mu * s.reducedPlanckConstant.val
  electron_angular_momentum :
    s.electron.angularMomentumMagnitude.val =
      s.mu * s.reducedPlanckConstant.val
  mu_eq_four : s.mu = 4
  bound_orbit_energy : s.totalEnergy.val < 0
  isolated_energy_at_initial_turning_point :
    s.totalEnergy.val =
      turningPointEnergyReadout s s.initialSeparation
  isolated_energy_at_outer_turning_point :
    s.totalEnergy.val =
      turningPointEnergyReadout s s.maximumSeparation
  outer_turning_point_branch :
    s.initialSeparation.val < s.maximumSeparation.val

/-! ## Requested result -/

/--
For `μ = 4`, the maximum electron--positron separation is
`(1600 / 9) a₀`.
-/
theorem maximum_separation_for_mu_four
    (s : CoulombPairSystem) (laws : CoulombPairLaws s) :
    s.maximumSeparation.val =
      (1600 / 9 : ℝ) * s.bohrRadius.val := by
  sorry

end IPhO2026Problem1B1
... [leading content omitted]
```

### Blueprint excerpt
```tex
Their velocities are
antiparallel and perpendicular to their separation.  Each particle has angular
momentum of magnitude mu*hbar about the center of mass.  The system is isolated,
classical, non-relativistic, and has only electrostatic interaction.  The Bohr
radius is a\_0 = 4*pi*epsilon\_0*hbar\textasciicircum{}2/(m*e\textasciicircum{}2), and k = 1/(4*pi*epsilon\_0).

Current subquestion:
For mu = 4 the pair is bound. Find the maximum electron-positron separation in units of a\_0.

\paragraph{Current subquestion.}
For mu = 4 the pair is bound. Find the maximum electron-positron separation in units of a\_0.

\paragraph{Recorded answer/context.}
r\_max = (1600/9)*a\_0.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-2.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_B\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_1_B_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_B_1.lean.md`
```markdown
and
  angular-momentum magnitude for each labeled particle.
- `CoulombPairSystem` retains the shared constants, initial and maximum
  separations, conserved energy, and dimensionless `μ`.
- `turningPointEnergyReadout` is the smallest local classical point-particle
  reduction needed because no matching Physlib two-body Coulomb orbit API was
  located.
- `CoulombPairLaws` packages explicit usable equations and inequalities rather
  than opaque regime flags.

Real numbers occur only as fixed-unit readouts of dimension-tagged quantities,
dimensionless `μ`, and the requested dimensionless numerical coefficient.

## Grounding gaps

- No matching Mathlib/Physlib declaration was found for the classical
  equal-mass, oppositely charged point-particle Coulomb effective energy or its
  outer-turning-point theorem.
- `RigidBody.angularMomentum` is not reusable for point particles.
- `Electromagnetism.EMSystem.coulombConstant` has the right scalar formula but
  does not preserve the dimensional role required here.
- Blueprint redraft request: attach
  `\lean{IPhO2026Problem1B1.maximum_separation_for_mu_four}` to the target
  theorem environment.  No source-physics redraft is otherwise needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_1.md`
```markdown
ogical space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 3. `IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`

- Compile status: passed
- Open sorries: 5
- Direct-check seconds: 22.326
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_B_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_2.md`

### Lean excerpt
```lean
≠ 0
  outgoing_velocity_is_radial :
    Tendsto
      (fun t => (separationRadius S t)⁻¹ • separationVector S t)
      atTop
      (nhds (‖S.asymptoticRelativeVelocity‖⁻¹ •
        S.asymptoticRelativeVelocity))

/--
The conic equation on an unbounded branch forces the limiting polar angle to
be `arccos (1 / eccentricity)`.  The range hypothesis selects the outgoing
branch rather than the other root of the cosine equation.
-/
theorem outgoing_polar_angle_of_hyperbolic_conic
    (eccentricity conicParameter : ℝ)
    (radius polarAngle : ℝ → ℝ)
    (outgoingPolarAngle : ℝ)
    (hEccentricity : 1 < eccentricity)
    (hConicParameter : 0 < conicParameter)
    (hRadiusPositive : ∀ t, 0 < radius t)
    (hConic :
      ∀ t, radius t =
        conicParameter / (1 - eccentricity * Real.cos (polarAngle t)))
    (hRadiusLimit : Tendsto radius atTop atTop)
    (hAngleLimit : Tendsto polarAngle atTop (nhds outgoingPolarAngle))
    (hOutgoingBranch : 0 ≤ outgoingPolarAngle ∧ outgoingPolarAngle ≤ Real.pi) :
    outgoingPolarAngle = Real.arccos (1 / eccentricity) := by
  sorry

/--
The source constants, initial angular momentum, energy relation, and supplied
eccentricity formula give eccentricity `7/2` when `μ = 15/2`.
-/
theorem eccentricity_at_mu_fifteen_halves
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    S.eccentricity = 7 / 2 := by
  sorry

/-- The outgoing branch therefore has polar angle `arccos (2/7)`. -/
theorem outgoing_polar_angle_at_mu_fifteen_halves
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    S.outgoingPolarAngle = Real.arccos (2 / 7) := by
  sorry

/--
Fig. 1b puts the initial positron velocity along the positive horizontal axis,
while the conic's polar zero-axis points downward.  The radial outgoing limit
therefore converts polar angle `θ∞` into signed deflection `θ∞ - π/2`.
-/
theorem fig1b_signed_deflection_from_polar_angle
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    signedDeflectionRadians S = S.outgoingPolarAngle - Real.pi / 2 := by
  sorry

/--
For `μ = 15/2`, the outgoing relative velocity is deflected clockwise, below
the initial positron line.  The last conjunct is a rounding certificate:
the signed angle in degrees rounds to `-16.60°` to two decimal places.
-/
theorem asymptotic_relative_velocity_angle
    (S : ScatteringScenario Q) (h : CoulombScatteringLaws S) :
    signedDeflectionRadians S =
        Real.arccos (2 / 7) - Real.pi / 2 ∧
      signedDeflectionRadians S < 0 ∧
      |radiansToDegrees (signedDeflectionRadians S) + 83 / 5| < 1 / 200 := by
  sorry

end IPhO2026_1_B_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
is isolated,
classical, non-relativistic, and has only electrostatic interaction.  The Bohr
radius is a\_0 = 4*pi*epsilon\_0*hbar\textasciicircum{}2/(m*e\textasciicircum{}2), and k = 1/(4*pi*epsilon\_0).

Current subquestion:
For mu = 15/2 the pair is unbound. Find the angle between the asymptotic relative velocity u\_infinity and the initial positron line of motion.

\paragraph{Current subquestion.}
For mu = 15/2 the pair is unbound. Find the angle between the asymptotic relative velocity u\_infinity and the initial positron line of motion.

\paragraph{Recorded answer/context.}
The signed deflection is -16.60 degrees, i.e. 16.60 degrees below the initial line of motion.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-2.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_B\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_1_B_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_B_2.lean.md`
```markdown
trajectories, conic quantities, screen orientation, and
  asymptotic relative velocity.
- `CoulombScatteringLaws` is the smallest local replacement for the missing
  two-body Coulomb-scattering API.  It uses reusable equations, inequalities,
  derivatives, and limits rather than opaque predicates.
- `outgoing_polar_angle_of_hyperbolic_conic` isolates the reusable analytic
  elimination step supplied by the polar-conic hint.

## Grounding gaps

- No matching Mathlib/Physlib API was found for an equal-mass,
  oppositely-charged classical two-body Coulomb hyperbola, its eccentricity
  law, or its outgoing asymptote theorem.
- Physlib's `RigidBody.angularMomentum` concerns continuum rigid bodies, not
  either point particle here.
- `Electromagnetism.EMSystem.coulombConstant` has the correct scalar formula
  but does not by itself preserve all dimensional roles of this model.
- Mathlib's `polarCoord` supplies a coordinate chart only; it does not state
  the physical conic equation or branch limit.
- Blueprint redraft request: attach
  `\lean{IPhO2026_1_B_2.asymptotic_relative_velocity_angle}` to
  `thm:physics:IPhO_2026_1_B_2:target`.  No physics-statement redraft is
  otherwise needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_2.md`
```markdown
ogical space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 4. `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`

- Compile status: passed
- Open sorries: 7
- Direct-check seconds: 11.604
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_C_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_1.md`

### Lean excerpt
```lean
U` under the square root is present in the
official solution and is also required by the numerical result in part C.2.
The generated blueprint's recorded-answer line omitted this factor.
-/
def minimumAngularFrequencyExpression
    (parameters : Parameters) (theta : ℝ) : ℝ :=
  let effectiveTheta := effectiveThresholdAngle theta
  let factor := angularFactor effectiveTheta
  let massEnergy :=
    parameters.oxygenAtomMass * parameters.speedOfLight.val ^ 2
  3 * massEnergy *
      (1 - Real.sqrt
        (1 - (2 * parameters.energyGap / (3 * massEnergy)) * factor)) /
    (parameters.reducedPlanckConstant * factor)

/-- The displayed expression is the lower root of the minimized energy equation. -/
theorem minimumAngularFrequencyExpression_energy_boundary
    {parameters : Parameters} {theta : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi) :
    photonEnergy parameters (minimumAngularFrequencyExpression parameters theta) =
      parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta
          (minimumAngularFrequencyExpression parameters theta) := by
  sorry

/-- An infimum threshold, when it exists, is unique. -/
theorem isDissociationThreshold_unique
    {parameters : Parameters} {theta threshold₁ threshold₂ : ℝ}
    (hThreshold₁ :
      IsDissociationThreshold parameters theta threshold₁)
    (hThreshold₂ :
      IsDissociationThreshold parameters theta threshold₂) :
    threshold₁ = threshold₂ := by
  sorry

/--
Physics formalization target for
`thm:physics:IPhO_2026_1_C_1:target`.

The explicit formula itself is proved to be the minimum required angular
frequency; no threshold formula is assumed as a governing law.
-/
theorem minimumAngularFrequency_isDissociationThreshold
    (parameters : Parameters) (theta : ℝ)
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi) :
    IsDissociationThreshold parameters theta
      (minimumAngularFrequencyExpression parameters theta) := by
  sorry

/--
Equivalent value form: any scalar already identified semantically as the
minimum dissociation frequency equals the explicit expression.
-/
theorem minimumAngularFrequency_eq
    (parameters : Parameters) (theta omegaMinimum : ℝ)
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hMinimum :
      IsDissociationThreshold parameters theta omegaMinimum) :
    omegaMinimum = minimumAngularFrequencyExpression parameters theta := by
  sorry

end IPhO2026Problem1C1
... [leading content omitted]
```

### Blueprint excerpt
```tex
\_gamma/c = hbar*omega/c.

Current subquestion:
Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m.

\paragraph{Current subquestion.}
Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m.

\paragraph{Recorded answer/context.}
For theta <= pi/2, omega\_min = 3*m*c\textasciicircum{}2*[1 - sqrt(1 - (Delta U/(3*m*c\textasciicircum{}2))*(2*sin(theta)\textasciicircum{}2 + 1))]/[hbar*(2*sin(theta)\textasciicircum{}2 + 1)]. For theta >= pi/2 use the same threshold evaluated at theta = pi/2.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-3.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_C\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_1_C_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_C_1.lean.md`
```markdown
qualities/inequalities and reusable elimination theorems.

## Grounding gaps

- No matching Physlib API was found for photon absorption followed by
  nonrelativistic two-fragment molecular dissociation. The local event
  structure and conservation equations are therefore necessary.
- Physlib's fixed `Constants.ℏ` cannot represent the symbolic arbitrary-unit
  parameter requested by the problem.
- The blueprint's recorded C.1 answer omits a factor `2` multiplying `ΔU`
  under the square root. The official `T1_solution.pdf` gives the factor `2`
  (its discriminant has
  `36ℏ²m²c⁴ + 24 ΔU m c² ℏ² (cos(2θ)-2)`), and the official C.2 expansion
  `ℏω_min - ΔU = (2-cos(2θ))(ΔU)²/(6mc²)` independently requires it.
  The Lean file follows the conservation laws and official solution rather
  than introducing a false energy law to reproduce the transcription error.

## Redraft requests

- Correct the recorded C.1 answer to include the factor `2` under the square
  root:
  `1 - sqrt(1 - (2 ΔU/(3mc²))(1 + 2 sin² θ))`.
- Add
  `\lean{IPhO2026Problem1C1.minimumAngularFrequency_isDissociationThreshold}`
  to the target theorem environment so marker synchronization can identify the
  formalization.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_1.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 5. `IPhO2026Problems/problem_IPhO_2026_1_C_2.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 17.051
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_C_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_2.md`

### Lean excerpt
```lean
mentum‖ ^ 2 / (4 * massSI setup.atomMass) +
        ‖momentumSI setup.oxygenAtomMomentum‖ ^ 2 / (2 * massSI setup.atomMass)

/-- Above a right angle, the C.1 threshold is the threshold at `π/2`. -/
def effectiveThresholdAngle (theta : ℝ) : ℝ := min theta (Real.pi / 2)

/-- The angular factor occurring after minimization over the fragment momentum. -/
def thresholdShapeFactor (theta : ℝ) : ℝ :=
  2 * Real.sin theta ^ 2 + 1

/--
The reusable content of part C.1, stated as the energy-balance equation for the
lower threshold root.  It is equivalent to the energy-conserving closed form and
also records the `θ ≥ π/2` branch through `effectiveThresholdAngle`.
-/
structure PreviousPartC1Threshold
    (setup : OzonePhotodissociation) : Prop where
  threshold_energy_nonnegative :
    0 ≤ energyInElectronVolts setup.thresholdPhotonEnergy
  threshold_balance :
    energyInElectronVolts setup.thresholdPhotonEnergy =
      energyInElectronVolts setup.energyGap +
        energyInElectronVolts setup.thresholdPhotonEnergy ^ 2 *
          thresholdShapeFactor
            (effectiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad) /
          (6 * restEnergyInElectronVolts setup.atomMass)
  lower_root_selection :
    energyInElectronVolts setup.thresholdPhotonEnergy ≤
      3 * restEnergyInElectronVolts setup.atomMass /
        thresholdShapeFactor
          (effectiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad)

/--
The scalar electronvolt readout of the requested quantity
`ℏ ω_min - ΔU`.
-/
def requestedExcessEnergyInElectronVolts
    (setup : OzonePhotodissociation) : ℝ :=
  actionSI setup.reducedPlanckConstant *
      angularFrequencySI setup.minimumAngularFrequency /
      energySI DimEnergy.electronVolt -
    energyInElectronVolts setup.energyGap

/--
For `θ = π/6`, `ΔU = 1.10 eV`, and `m = 16.0 amu`, the threshold excess
energy rounds to `2.03 × 10⁻¹¹ eV` to three significant figures.

The radius `5 × 10⁻¹⁴ eV` is half a unit in the last reported decimal place;
it encodes rounding of the answer, not experimental uncertainty.
-/
theorem threshold_excess_energy_rounds_to_official_value
    (setup : OzonePhotodissociation)
    (_laws : ClassicalPhotodissociationLaws setup)
    (_previousPart : PreviousPartC1Threshold setup)
    (angle_readout :
      setup.outgoingOxygenMoleculeAngleRad = Real.pi / 6)
    (energy_gap_readout :
      energyInElectronVolts setup.energyGap = 1.10)
    (atom_mass_readout :
      massInAtomicMassUnits setup.atomMass = 16.0) :
    abs (requestedExcessEnergyInElectronVolts setup - 2.03e-11) ≤ 5e-14 := by
  sorry

end IPhO2026_1_C_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
rded answer/context.}
hbar*omega\_min - Delta U = 2.03e-11 eV.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.1. Question: Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m. Reusable conclusions: For theta <= pi/2, omega\_min = 3*m*c\textasciicircum{}2*[1 - sqrt(1 - (Delta U/(3*m*c\textasciicircum{}2))*(2*sin(theta)\textasciicircum{}2 + 1))]/[hbar*(2*sin(theta)\textasciicircum{}2 + 1)]. For theta >= pi/2 use the same threshold evaluated at theta = pi/2. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_C\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_1_C_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_C_2.lean.md`
```markdown
e natural-language C.1
  result without importing or depending on the sibling Lean output.

Real numbers occur only as SI/unit readouts, radians, dimensionless
trigonometric values, vector coordinates, and the final numerical answer.

## Grounding gaps and redraft requests

- No Physlib atomic-mass-unit constant was found, so `atomicMassUnit` is local.
- The chapter's recorded C.1 closed form omits a factor `2` multiplying `ΔU`
  under the square root. As printed, its small-`ΔU` limit is `ΔU/2` and, for
  the C.2 data, it predicts a photon threshold near `0.55 eV`, contradicting
  `E_γ ≥ ΔU`, energy conservation, and the recorded C.2 answer. The Lean
  contract therefore uses the energy-conserving equivalent quadratic
  `E = ΔU + E²(1 + 2 sin² θ_eff)/(6mc²)`, whose explicit lower root contains
  the missing factor `2`. The blueprint/source-report C.1 answer should be
  corrected.
- The blueprint target environment should name the main Lean theorem as noted
  above.
- The prompt advertised `archon dag-query`, but `archon` was not available on
  this lane's shell `PATH`; dependency-graph inspection was therefore blocked.
  This does not affect the independent statement formalization.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_2.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 6. `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 17.505
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_A_1.md`

### Lean excerpt
```lean
ing : LimitingRayWitness experiment N xN) : Prop where
  angle_closure :
    (2 * (N : ℝ) + 1) * limiting.firstImpactPolarAngle = Real.pi

/-- The governing-law interface needed from geometric optics. Besides the
local equal-angle law, it exposes the limiting-ray projection and angular
closure that follow from applying that law to the circular mirror. -/
structure HalfCylinderReflectionLaws {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) : Prop where
  obeys_specular_reflection : ObeysSpecularReflection experiment
  limiting_ray_geometry :
    ∀ (N : ℕ) (xN : ℝ),
      0 < N →
      IsPositiveReflectionThreshold experiment N xN →
      ∃ limiting : LimitingRayWitness experiment N xN,
        HalfCircleProjectionGeometry experiment N xN limiting ∧
          RepeatedReflectionClosure experiment N xN limiting

/-- Algebraic bridge from the repeated-reflection closure to the unique
limiting angle. -/
lemma limiting_first_impact_angle {mirror : HalfCylindricalMirror}
    {experiment : MultipleReflectionExperiment mirror} {N : ℕ} {xN : ℝ}
    (hN : 0 < N) (limiting : LimitingRayWitness experiment N xN)
    (closure : RepeatedReflectionClosure experiment N xN limiting) :
    limiting.firstImpactPolarAngle =
      Real.pi / (2 * (N : ℝ) + 1) := by
  sorry

/-- The two angles occurring in the official sine and cosine answer forms are
complementary. -/
lemma official_answer_angles_complementary (N : ℕ) (hN : 0 < N) :
    Real.pi / 2 - Real.pi / (2 * (N : ℝ) + 1) =
      (2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2) := by
  sorry

/-- Trigonometric bridge between the two official closed forms. The Mathlib
carrier for the complementary-angle step is `Real.sin_pi_div_two_sub`. -/
lemma official_sine_cosine_forms_agree (N : ℕ) (hN : 0 < N) :
    Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) =
      Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  sorry

/-- IPhO 2026 Problem 2 A.1: the positive threshold for at most `N`
reflections in the half-cylindrical mirror has the two equivalent official
closed forms. -/
theorem positive_reflection_threshold_formula
    {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror)
    (laws : HalfCylinderReflectionLaws experiment)
    (N : ℕ) (hN : 0 < N) (xN : ℝ)
    (hThreshold : IsPositiveReflectionThreshold experiment N xN) :
    xN =
        mirror.radius *
          Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) ∧
      xN =
        mirror.radius *
          Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  sorry

end IPhO2026Problem2A1
... [leading content omitted]
```

### Blueprint excerpt
```tex
l rays strike the inside of a half-cylindrical mirror of radius R.  For
an incident ray with transverse coordinate x, let N be its number of
reflections.  The positive threshold x\_N is the largest distance from the
optical axis for which a ray undergoes at most N reflections.  Use Figures
2c--2e for the mirror and limiting-ray geometry.

Current subquestion:
Find the general expression for the threshold x\_N in terms of R and the positive integer N.

\paragraph{Current subquestion.}
Find the general expression for the threshold x\_N in terms of R and the positive integer N.

\paragraph{Recorded answer/context.}
x\_N = R*sin((2*N - 1)*pi/(4*N + 2)) = R*cos(pi/(2*N + 1)).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-2.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_A\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_A_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_A_1.lean.md`
```markdown
hysical
  meaning without inventing a nonexistent optics API.
- `SourceFigure` preserves the explicit 2c/2d/2e figure labels in the Lean
  vocabulary.

## Grounding gaps and redraft requests

- **Optics API gap:** no ready-made PhysLean/Mathlib carrier was found for
  curved-mirror specular ray tracing with an impact count. The faithful local
  interfaces above are used instead.
- **Dependency navigation gap:** the prompt advertised `archon dag-query`, but
  `archon` was not on `PATH` in this lane. The blueprint shows no dependency
  annotations or previous parts, so this caused no sibling dependency to be
  introduced.
- **Lake target-registration gap:** the project registers only the
  `IPhO2026Run` library, so
  `lake build IPhO2026Problems.problem_IPhO_2026_2_A_1` reports an unknown
  target. Direct verification with
  `lake env lean IPhO2026Problems/problem_IPhO_2026_2_A_1.lean` succeeds with
  exactly four expected `sorry` warnings and no errors.
- **Blueprint redraft request:** the chapter records the answer but not the
  informal equal-angle derivation of `(2N+1)θ = π`. A later planning/review pass
  should flesh out that geometric bridge and add the Lean declaration links.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_A_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 7. `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`

- Compile status: passed
- Open sorries: 5
- Direct-check seconds: 16.658
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_B_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_1.md`

### Lean excerpt
```lean
t_radius_eq_signedDistance
    (setup : SolarCookerSetup) (origin direction : CrossSection)
    (hTangent : LimitingTangentRay setup origin direction) :
    setup.containerRadius.val =
      cross2D direction (setup.containerCenterMeters - origin) := by
  sorry

/--
For the maximum-incidence ray in the ray model, the actual container radius
equals the canonical limiting-radius readout.
-/
theorem maximum_ray_containerRadius_eq_limitingRadius
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup)
    (law : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (hMax : IsMaximumIncidenceAngle model thetaMax) :
    setup.containerRadius.val = limitingRadiusMeters setup thetaMax := by
  sorry

/--
Expanding the canonical incidence point, specular-reflection equation, and
center offset from Figure 2f gives the two-term trigonometric radius formula.
-/
theorem limitingRadiusMeters_eq_trigFormula
    (setup : SolarCookerSetup) (theta : ℝ) :
    limitingRadiusMeters setup theta =
      setup.mirrorRadius.val * Real.sin theta -
        (setup.mirrorRadius.val / 2) * Real.sin (2 * theta) := by
  sorry

/--
`alpha` and `beta` are the two universal coefficients of the limiting-radius
function, rather than two arbitrary unknowns satisfying one numerical equation.
This functional reading is the coefficient-identification content of B.1.
-/
def AreTrigCoefficients
    (setup : SolarCookerSetup) (alpha beta : Length) : Prop :=
  ∀ theta,
    alpha.val * Real.sin theta + beta.val * Real.sin (2 * theta) =
      limitingRadiusMeters setup theta

/--
The answer to IPhO 2026 problem 2, part B.1:
`alpha = R` and `beta = -R/2`.

The hypothesis `givenRadiusRelation` records the equation printed in the
question at the actual `thetaMax`.  `coefficientIdentity` records that
`alpha,beta` are the coefficients of the whole geometry-derived expression;
without that symbolic coefficient interpretation, one equation at one angle
would underdetermine two coefficients.
-/
theorem coefficients_from_solar_cooker_geometry
    (setup : SolarCookerSetup) (model : SolarOpticsModel setup)
    (tangencyLaw : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (thetaMax_is_maximum : IsMaximumIncidenceAngle model thetaMax)
    (alpha beta : Length)
    (givenRadiusRelation :
      setup.containerRadius.val =
        alpha.val * Real.sin thetaMax + beta.val * Real.sin (2 * thetaMax))
    (coefficientIdentity : AreTrigCoefficients setup alpha beta) :
    alpha = setup.mirrorRadius ∧
      beta = scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius := by
  sorry

end

end IPhO2026_2_B_1

end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
er lies
R/2 from the mirror center on the symmetry plane.  Uniform parallel sunlight
arrives along the optical axis.  Any ray absorbed by the container reflects at
most once.  Let theta\_max be the largest incidence angle on the mirror among
rays that strike the container, and let P\_0 be the power the cylinder would
receive without the mirror.  See Figure 2f.

Current subquestion:
Given a = alpha*sin(theta\_max) + beta*sin(2*theta\_max), determine alpha and beta in terms of R.

\paragraph{Current subquestion.}
Given a = alpha*sin(theta\_max) + beta*sin(2*theta\_max), determine alpha and beta in terms of R.

\paragraph{Recorded answer/context.}
alpha = R and beta = -R/2.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-3.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_B\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_B_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_B_1.lean.md`
```markdown
dge.
- `AreTrigCoefficients`: captures the symbolic meaning of “determine the coefficients” without assuming their values.

These abstractions use real numbers only for coordinate, angle, and unit readouts. Physical lengths, power, and irradiance remain dimension-tagged.

## Grounding gaps

- Mathlib/PhysLean currently provides generic Euclidean reflection and algebraic rays, but the search did not locate a geometric-optics API for incident/reflected light rays at a curved mirror. The exact specular equation is therefore encoded locally.
- No ready-made PhysLean declarations for power and irradiance dimensions were found; their standard dimension exponent vectors are encoded locally.
- The `archon dag-query` navigation command was unavailable on this prover process's `PATH`. The blueprint declares no `\uses` dependencies and the source report has no previous parts, so this did not create a dependency gap.

## Redraft requests

- None. The statement is proof-ready at the autoformalize level.

## Verification

- Lean LSP diagnostics: no errors; five expected `sorry` warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`: exit code 0; five expected `sorry` warnings.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 8. `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 11.459
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_2.tex`
- Reports: `.archon/task_results/problem_IPhO_2026_2_B_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_2.md`

### Lean excerpt
```lean
.reflectedFromMirror ray → s.strikesContainer ray →
      0 ≤ s.incidenceAngleToNormal ray
  thetaMax_is_upper_bound :
    ∀ ray, s.reflectedFromMirror ray → s.strikesContainer ray →
      s.incidenceAngleToNormal ray ≤ s.thetaMax
  thetaMax_is_attained :
    ∃ ray, s.reflectedFromMirror ray ∧ s.strikesContainer ray ∧
      s.incidenceAngleToNormal ray = s.thetaMax

/--
Power accounting for constant uniform irradiance.

The two width equations are the Figure 2f projected-aperture readouts.  The two
power equations state that a fully absorbed parallel beam carries irradiance
times projected area, with the common projected area written as width times
axial length.  None of these fields states the requested final ratio.
-/
structure Figure2fPowerBalance {Ray : Type} (s : Figure2fSetup Ray) : Prop where
  irradiance_pos : 0 < s.solarIrradiance.val
  no_mirror_projected_width :
    s.noMirrorProjectedWidth.val = 2 * s.containerRadius.val
  actual_projected_width :
    s.actualProjectedWidth.val =
      2 * s.mirrorRadius.val * Real.sin s.thetaMax
  no_mirror_power_balance :
    s.noMirrorPower.val =
      s.solarIrradiance.val * s.noMirrorProjectedWidth.val * s.axialLength.val
  actual_power_balance :
    s.receivedPower.val =
      s.solarIrradiance.val * s.actualProjectedWidth.val * s.axialLength.val

/--
Part B.1 and the double-angle identity rewrite the container radius in a form
that displays the factor which will cancel against the collected aperture.
-/
theorem container_radius_factorization {Ray : Type} (s : Figure2fSetup Ray)
    (hB1 : PreviousPartB1Result s) :
    s.containerRadius.val =
      s.mirrorRadius.val * Real.sin s.thetaMax *
        (1 - Real.cos s.thetaMax) := by
  sorry

/--
The common irradiance and axial extent cancel, so the power ratio equals the
ratio of the two projected widths.
-/
theorem power_ratio_eq_projected_width_ratio {Ray : Type} (s : Figure2fSetup Ray)
    (hGeometry : Figure2fGeometry s) (hPower : Figure2fPowerBalance s) :
    s.receivedPower.val / s.noMirrorPower.val =
      s.actualProjectedWidth.val / s.noMirrorProjectedWidth.val := by
  sorry

/--
For the Figure 2f solar cooker, the actual-to-no-mirror received-power ratio is
`1 / (1 - cos θ_max)`.
-/
theorem power_ratio_eq_one_div_one_sub_cos {Ray : Type} (s : Figure2fSetup Ray)
    (hGeometry : Figure2fGeometry s)
    (hB1 : PreviousPartB1Result s)
    (hRays : ValidFigure2fRayOptics s)
    (hPower : Figure2fPowerBalance s) :
    s.receivedPower.val / s.noMirrorPower.val =
      1 / (1 - Real.cos s.thetaMax) := by
  sorry

end IPhO_2026_2_B_2
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
strike the container, and let P\_0 be the power the cylinder would
receive without the mirror.  See Figure 2f.

Current subquestion:
Express the power ratio P/P\_0 in terms of theta\_max.

\paragraph{Current subquestion.}
Express the power ratio P/P\_0 in terms of theta\_max.

\paragraph{Recorded answer/context.}
P/P\_0 = 1/(1 - cos(theta\_max)).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.1. Question: Given a = alpha*sin(theta\_max) + beta*sin(2*theta\_max), determine alpha and beta in terms of R. Reusable conclusions: alpha = R and beta = -R/2. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_B\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_B_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `problem_IPhO_2026_2_B_2.lean.md`
```markdown
cylinder length implicit in the apparatus and cancels
  from the ratio.
- Rays remain an abstract type because no Physlib geometric-optics ray model
  matching the problem was found; all source-relevant consequences are exposed
  as fields rather than hidden behind an opaque relation.

## Grounding gaps

- LeanExplore found generic `EuclideanGeometry.reflection`, `RayVector`, and
  `Module.Ray`, but no ready-made Physlib law for specular cylindrical-mirror
  ray collection or uniform-irradiance projected-aperture power. The local
  interfaces encode exactly the equations needed here.
- The optional `archon dag-query` executable was not available on `PATH`, so
  the blueprint dependency graph could not be queried. The chapter itself
  lists only B.1 as a natural-language prerequisite, which is represented
  locally without a Lean import.

## Verification

- `mcp__archon_lean_lsp.lean_diagnostic_messages`: no errors; exactly three
  expected `declaration uses sorry` warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`: exit code 0;
  exactly the same three expected warnings.
- `archon-protected.yaml` contains no active protected declaration affecting
  this file.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_2.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 9. `IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 11.311
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_B_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_3.md`

### Lean excerpt
```lean
in the one-reflection regime.
-/
structure PreviousPartResults
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity) : Prop where
  radius_from_cutoff_ray :
    lengthInMetres cooker.containerRadius =
      lengthInMetres cooker.mirrorRadius * Real.sin cooker.thetaMax -
        (lengthInMetres cooker.mirrorRadius / 2) *
          Real.sin (2 * cooker.thetaMax)
  power_ratio_from_cutoff_angle :
    powerInWatts actualPower / powerInWatts baselinePower =
      1 / (1 - Real.cos cooker.thetaMax)

/--
At a fivefold power gain over a positive baseline, the B.2 power law forces
`cos θ_max = 4/5`.
-/
theorem cosine_thetaMax_of_fivefold_power
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    Real.cos cooker.thetaMax = (4 : ℝ) / 5 := by
  sorry

/--
Using both previous-part laws and the nonnegative incidence-angle branch,
`R = 1 m` together with a fivefold power gain forces the requested container
radius.
-/
theorem container_radius_of_fivefold_power
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (figure : Figure2fAssumptions cooker)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (mirrorRadius_eq_one_metre :
      lengthInMetres cooker.mirrorRadius = 1)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    lengthInMetres cooker.containerRadius = (12 : ℝ) / 100 ∧
      lengthInCentimetres cooker.containerRadius = 12 := by
  sorry

/--
Answer to IPhO 2026 theoretical problem 2, part B.3: the operating point has
`cos θ_max = 4/5`, and the required radius is `0.12 m = 12 cm`.
-/
theorem ipho2026_problem2_B3
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (figure : Figure2fAssumptions cooker)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (mirrorRadius_eq_one_metre :
      lengthInMetres cooker.mirrorRadius = 1)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    Real.cos cooker.thetaMax = (4 : ℝ) / 5 ∧
      lengthInMetres cooker.containerRadius = (12 : ℝ) / 100 ∧
      lengthInCentimetres cooker.containerRadius = 12 := by
  sorry

end

end IPhO2026Problem2B3
... [leading content omitted]
```

### Blueprint excerpt
```tex
ind a such that P = 5*P\_0, and report it in cm.

\paragraph{Recorded answer/context.}
cos(theta\_max) = 4/5 and a = 0.12 m = 12 cm.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.1. Question: Given a = alpha*sin(theta\_max) + beta*sin(2*theta\_max), determine alpha and beta in terms of R. Reusable conclusions: alpha = R and beta = -R/2. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\item Source B.2. Question: Express the power ratio P/P\_0 in terms of theta\_max. Reusable conclusions: P/P\_0 = 1/(1 - cos(theta\_max)). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_B\_3.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_B_3:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_B_3.lean.md`
```markdown
t
  entirely from Physlib dimension primitives.
- `SolarCooker` retains apparatus quantities, directions, absorptivity,
  reflection count, and the cutoff angle.
- `Figure2fAssumptions` exposes every local physical/setup assertion as a
  mathematical equation or inequality.
- `PreviousPartResults` faithfully restates the allowed natural-language B.1
  and B.2 prerequisites without a forbidden sibling import.

## Grounding gaps

- No dedicated half-cylindrical solar-mirror/cutoff-ray API was identified in
  Mathlib or Physlib. The local apparatus and law interfaces preserve the
  necessary geometry and provide direct elimination equations.
- No ready-made named radiant-power or irradiance dimension was selected; the
  standard dimensions are composed locally from Physlib base dimensions.
- The `archon dag-query` executable was unavailable on this lane's `PATH`, so
  the dependency graph could not be queried. The blueprint explicitly marks
  both previous parts as natural-language-only prerequisites, so no sibling
  Lean dependency was introduced.

## Redraft requests

- None. The formal contract is compiling, dimension-aware, proof-ready, and
  contains no current-answer hypothesis.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_3.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 10. `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 10.258
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_1.md`

### Lean excerpt
```lean
er caustic construction: ray B is parallel to
ray A, has incidence angle `theta + deltaTheta`, and intersects ray A's
reflected line at the sampled caustic point.  `relativeScale` makes the
informal condition `Δθ ≪ θ` explicit without choosing an unstated numerical
tolerance. -/
structure Figure2gCausticSetup
    (mirror : HalfCylindricalMirror) (theta : ℝ) where
  rayA : Figure2gRayInteraction mirror theta
  deltaTheta : ℝ
  deltaTheta_pos : 0 < deltaTheta
  relativeScale : ℝ
  relativeScale_pos : 0 < relativeScale
  relativeScale_lt_one : relativeScale < 1
  deltaTheta_small_relative :
    |deltaTheta| ≤ relativeScale * |theta|
  rayB : Figure2gRayInteraction mirror (theta + deltaTheta)
  incoming_rays_parallel :
    rayB.incidentRay.propagationDirection =
      rayA.incidentRay.propagationDirection
  causticSamplePoint : PlanePoint
  caustic_point_on_reflected_rayA :
    rayA.reflectedLine.Contains causticSamplePoint
  caustic_point_on_reflected_rayB :
    rayB.reflectedLine.Contains causticSamplePoint

/-- The vector reflection law and Figure 2g orientation select the outgoing
down-left branch and give its doubled-angle direction. -/
theorem reflected_direction_from_specular_law
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    interaction.reflectedRay.propagationDirection =
      { dx := -Real.sin (2 * incidenceAngle)
        dy := -Real.cos (2 * incidenceAngle) } := by
  sorry

/-- The direction equation of the reflected supporting line determines its
dimensionless slope. -/
theorem reflected_line_slope
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    interaction.mA = Real.cot (2 * incidenceAngle) := by
  sorry

/-- Incidence of the reflected line at the mirror hit point determines its
length-valued intercept. -/
theorem reflected_line_intercept
    (mirror : HalfCylindricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    interaction.bA = mirror.radius / (2 * Real.cos incidenceAngle) := by
  sorry

/-- **IPhO 2026, Problem 2, C.1.**  In the Figure 2g coordinate convention,
the reflected ray A has slope `cot (2 * theta)` and intercept
`R / (2 * cos theta)`. -/
theorem rayA_slope_and_intercept
    (mirror : HalfCylindricalMirror) (theta : ℝ)
    (setup : Figure2gCausticSetup mirror theta) :
    setup.rayA.mA = Real.cot (2 * theta) ∧
      setup.rayA.bA = mirror.radius / (2 * Real.cos theta) := by
  sorry

end IPhO2026_2_C_1
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
ical mirror of radius R, ray A is incident at angle theta
and its reflected line is y = m\_A*x + b\_A.  A neighboring parallel ray B is
incident at theta + Delta theta, with Delta theta much smaller than theta, and
its reflected line is y = m\_B*x + b\_B.  The envelope/intersection of neighboring
rays forms the caustic.  Use Figure 2g and its coordinate convention.

Current subquestion:
Write the slope m\_A and intercept b\_A of reflected ray A in terms of theta and R.

\paragraph{Current subquestion.}
Write the slope m\_A and intercept b\_A of reflected ray A in terms of theta and R.

\paragraph{Recorded answer/context.}
m\_A = cot(2*theta), and b\_A = R/(2*cos(theta)).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-4.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_C\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_C_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_1.lean.md`
```markdown
ps

- `Module.Ray` is an equivalence class of nonzero module vectors under
  positive scaling; it does not retain a hit point, a mirror normal, or a
  reflected supporting line, so it is not a complete optical-ray carrier here.
- `EuclideanGeometry.reflection` reflects points in affine subspaces. The
  problem needs a propagation-direction reflection at the tangent plane of a
  curved mirror, so the direct component law is the faithful smaller
  interface.
- No dedicated specular-optics or half-cylindrical-mirror API was found in the
  searched Mathlib/Physlib surface or by local PhysLean source search.
- The source gives only the qualitative notation `Δθ ≪ θ`; the formalization
  therefore exposes a relative-scale witness `ε` rather than inventing a
  numerical tolerance.
- `archon dag-query` was unavailable on this lane's `PATH`. The source has no
  previous-part dependencies, so no sibling import or hidden dependency was
  introduced.

## Redraft requests

- The blueprint target environment currently has no `\lean{...}` declaration
  association. The synchronization/review step should attach the main theorem
  name above; no change to the informal physics statement is requested.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 11. `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 16.308
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_2.md`

### Lean excerpt
```lean
act coefficient consequence of specular reflection from the circular
mirror at an arbitrary incidence angle.  C.2 applies this governing law at
`θ + Δθ` and then takes its first-order expansion. -/
def SatisfiesHalfCylindricalSpecularLaw
    (mirror : HalfCylindricalMirror) (ray : OpticalRay2D) : Prop :=
  ray.reflectedLine.slope =
      Real.cot (2 * ray.incidenceAngle) ∧
    ray.reflectedLine.yIntercept =
      mirror.radius / (2 * Real.cos ray.incidenceAngle)

/-- The exact slope equation exposed by the circular-mirror reflection law. -/
theorem slope_eq_of_specular_law
    {mirror : HalfCylindricalMirror} {ray : OpticalRay2D}
    (h : SatisfiesHalfCylindricalSpecularLaw mirror ray) :
    ray.reflectedLine.slope = Real.cot (2 * ray.incidenceAngle) :=
  h.1

/-- The exact intercept equation exposed by the circular-mirror reflection law. -/
theorem intercept_eq_of_specular_law
    {mirror : HalfCylindricalMirror} {ray : OpticalRay2D}
    (h : SatisfiesHalfCylindricalSpecularLaw mirror ray) :
    ray.reflectedLine.yIntercept =
      mirror.radius / (2 * Real.cos ray.incidenceAngle) :=
  h.2

/-- IPhO 2026 Problem 2 C.2: the reflected line of the neighboring ray `B`
has the stated first-order slope and intercept expansions as `Δθ → 0`.

The two `IsBigO` conclusions say that the displayed remainders are bounded by
a constant multiple of `Δθ²` near zero.  Thus the approximation order in the
source is part of the theorem contract rather than being silently discarded. -/
theorem rayB_firstOrderExpansion
    (mirror : HalfCylindricalMirror) (θ : ℝ)
    (rayA : OpticalRay2D) (rayB : ℝ → OpticalRay2D)
    (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi / 2)
    (hsin : Real.sin (2 * θ) ≠ 0) (hcos : Real.cos θ ≠ 0)
    (hA_geometry : HasFigure2gGeometry mirror Figure2gRayLabel.A θ rayA)
    (hB_geometry :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ),
        HasFigure2gGeometry mirror Figure2gRayLabel.B (θ + Δθ) (rayB Δθ))
    (h_parallel :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ), HaveParallelIncomingDirections rayA (rayB Δθ))
    (hC1 : SatisfiesPreviousPartC1 mirror θ rayA)
    (h_reflection :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ),
        SatisfiesHalfCylindricalSpecularLaw mirror (rayB Δθ)) :
    ((fun Δθ : ℝ =>
        (rayB Δθ).reflectedLine.slope -
          (Real.cot (2 * θ) -
            2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ))
        =O[𝓝 (0 : ℝ)] (fun Δθ : ℝ => Δθ ^ 2)) ∧
      ((fun Δθ : ℝ =>
        (rayB Δθ).reflectedLine.yIntercept -
          (mirror.radius / (2 * Real.cos θ) *
            (1 + Real.tan θ * Δθ)))
        =O[𝓝 (0 : ℝ)] (fun Δθ : ℝ => Δθ ^ 2)) := by
  sorry

end IPhO2026Problems.IPhO2026_2_C_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
pand m\_B and b\_B to first order in Delta theta.

\paragraph{Current subquestion.}
Expand m\_B and b\_B to first order in Delta theta.

\paragraph{Recorded answer/context.}
m\_B = cot(2*theta) - 2*csc(2*theta)\textasciicircum{}2*Delta theta; b\_B = [R/(2*cos(theta))]*(1 + tan(theta)*Delta theta), up to O(Delta theta\textasciicircum{}2).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-4.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.1. Question: Write the slope m\_A and intercept b\_A of reflected ray A in terms of theta and R. Reusable conclusions: m\_A = cot(2*theta), and b\_A = R/(2*cos(theta)). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_C\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_C_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_2.lean.md`
```markdown
, incoming/outgoing directions,
  figure label, and reflected-line readout.
- `HalfCylindricalMirror` retains the positive-radius physical object.
- The geometry, previous-part, parallelism, and reflection predicates are the
  smallest local interfaces needed to expose the equations and inequalities
  used by a future proof.

Real numbers are used only for radians, dimensionless slopes/direction
components, and scalar coordinate/length readouts, as permitted by the source.

## Grounding gaps

- PhysLean has no located geometric-optics abstraction matching a ray reflected
  by a half-cylindrical mirror. The locally encoded exact coefficient law is
  therefore necessary.
- LeanExplore did not return a single theorem that directly packages the two
  required trigonometric first-order expansions with quadratic `IsBigO`
  remainders. This is not a statement-level blocker: the exact equations,
  nonsingularity conditions, derivative declarations, and asymptotic target
  are all present for the later proof.
- Blueprint redraft request: add
  `\lean{IPhO2026Problems.IPhO2026_2_C_2.rayB_firstOrderExpansion}` to the
  target theorem environment. No source physics redraft is otherwise needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_2.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 12. `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`

- Compile status: passed
- Open sorries: 6
- Direct-check seconds: 17.402
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_3.md`

### Lean excerpt
```lean
ngle θ) :
    HasFigure2gFirstOrderExpansions R θ := by
  sorry

/-- The intersection of two distinct affine support lines, written in Figure
2g coordinates.  This is an algebraic bridge, not the limiting caustic
formula. -/
def supportIntersectionCandidate (R α β : ℝ) : PlanarPoint :=
  let x :=
    (reflectedIntercept R β - reflectedIntercept R α) /
      (reflectedSlope α - reflectedSlope β)
  planarPoint x (reflectedSlope α * x + reflectedIntercept R α)

/-- On the admissible branch, increasing the incidence angle changes the
reflected slope, so neighboring support lines are distinct. -/
theorem reflectedSlope_ne_of_angle_lt
    {α β : ℝ}
    (hα : IsAdmissibleAngle α)
    (hβ : IsAdmissibleAngle β)
    (hαβ : α < β) :
    reflectedSlope α ≠ reflectedSlope β := by
  sorry

/-- Ray membership and the C.1 support-line law determine the finite
neighboring-ray intersection uniquely. -/
theorem neighboringIntersection_eq_supportIntersectionCandidate
    {R θ δ : ℝ}
    (model : Figure2gOptics R)
    (p : PlanarPoint)
    (hIntersection : IsNeighboringReflectedIntersection model θ δ p) :
    p = supportIntersectionCandidate R θ (θ + δ) := by
  sorry

/-- Pure analytic bridge: the intersections of the C.1 support lines tend to
the displayed caustic point as the positive angular separation tends to zero.
The proof obligation includes the trigonometric simplification of both
coordinates. -/
theorem supportIntersectionCandidate_tendsto
    (R θ : ℝ)
    (hθ : IsAdmissibleAngle θ) :
    Tendsto
      (fun δ : ℝ => supportIntersectionCandidate R θ (θ + δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (planarPoint
        (R * Real.sin θ ^ 3)
        ((R / 2) * Real.cos θ * (2 - Real.cos (2 * θ))))) := by
  sorry

/-- IPhO 2026 problem 2, part C.3: the limiting intersection coordinates of
neighboring reflected rays are
`X_c = R sin(θ)^3` and
`Y_c = (R/2) cos(θ) (2 - cos(2θ))`.

The intersection function is constrained only by actual membership in both
outgoing reflected rays for all sufficiently small positive separations. -/
theorem limitingIntersectionCoordinates
    {R θ δMax : ℝ}
    (model : Figure2gOptics R)
    (intersection : ℝ → PlanarPoint)
    (hθ : IsAdmissibleAngle θ)
    (hδMax : 0 < δMax)
    (hAngleWindow : θ + δMax < Real.pi / 2)
    (hIntersection :
      ∀ δ, 0 < δ → δ < δMax →
        IsNeighboringReflectedIntersection model θ δ (intersection δ)) :
    Tendsto intersection
      (𝓝[>] (0 : ℝ))
      (𝓝 (planarPoint
        (R * Real.sin θ ^ 3)
        ((R / 2) * Real.cos θ * (2 - Real.cos (2 * θ))))) := by
  sorry

end
end IPhO2026_2_C_3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
agraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-4.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.1. Question: Write the slope m\_A and intercept b\_A of reflected ray A in terms of theta and R. Reusable conclusions: m\_A = cot(2*theta), and b\_A = R/(2*cos(theta)). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\item Source C.2. Question: Expand m\_B and b\_B to first order in Delta theta. Reusable conclusions: m\_B = cot(2*theta) - 2*csc(2*theta)\textasciicircum{}2*Delta theta; b\_B = [R/(2*cos(theta))]*(1 + tan(theta)*Delta theta), up to O(Delta theta\textasciicircum{}2). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_C\_3.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_C_3:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_3.lean.md`
```markdown
half-cylindrical-mirror/reflection API was found.  Its fields expose
  the geometry and affine reflection equations used by later proofs.
- `IsNeighboringReflectedIntersection` packages the positive neighboring-angle
  branch and membership in both outgoing rays without asserting any limit.
- `HasFigure2gFirstOrderExpansions` packages the two rigorous C.2 asymptotic
  bounds.

These abstractions preserve the physical roles and expose all mathematical
consequences needed to derive the target.

## Grounding gaps

- No ready-made Physlib API for an oriented geometrical-optics ray, a
  half-cylindrical mirror, specular reflection in Figure 2g coordinates, or a
  caustic envelope was found.  The explicit local interfaces above fill this
  gap without assuming the current answer.
- Mathlib exposes cotangent but no candidate was needed for a separate cosecant
  object; `csc(2θ)^2` is faithfully represented as
  `1 / Real.sin (2 * θ) ^ 2`.
- The `archon` DAG helper was unavailable on this lane's shell `PATH`; this did
  not block formalization because the chapter gives no Lean dependency links
  and sibling outputs were prohibited by the previous-part policy.

No redraft request is needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_3.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 13. `IPhO2026Problems/problem_IPhO_2026_2_C_4.lean`

- Compile status: passed
- Open sorries: 2
- Direct-check seconds: 16.96
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_4.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_4.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_4.md`

### Lean excerpt
```lean
ayEnvelope :
    FormsNeighboringRayCaustic reflectedRay intersectionXReadout
      intersectionYReadout causticXReadout causticYReadout
  previousPartC3 :
    HasPreviousPartC3Coordinates frame causticXReadout causticYReadout

/-- Figure label A: the reflected member of the family incident at `θ`. -/
def reflectedRayA (model : Figure2gCausticModel) (θ : ℝ) :
    ReflectedRayReadout :=
  model.reflectedRay θ

/--
Figure label B: the neighboring reflected member incident at `θ + Δθ`.
-/
def reflectedRayB (model : Figure2gCausticModel) (θ Δθ : ℝ) :
    ReflectedRayReadout :=
  model.reflectedRay (θ + Δθ)

/--
Candidate parameters for a leading small-angle power law
`Y_c = v |X_c|^(p/q) + u`.

`uReadout` is a length readout.  `vScaleReadout` is the numerical coefficient
in the selected length unit; for the answer `p/q = 2/3`, it has the associated
dimensional role `length^(1/3)`.
-/
structure CausticPowerLawParameters where
  uReadout : ℝ
  vScaleReadout : ℝ
  exponentNumerator : ℕ
  exponentDenominator : ℕ

/--
The rigorous meaning of the source's small-angle normal form: after removing
the vertical offset, the two sides are asymptotically equivalent as `θ → 0`
through nonzero angles.  The exponent is required to be a reduced fraction.
-/
def HasSmallAnglePowerLaw
    (model : Figure2gCausticModel)
    (parameters : CausticPowerLawParameters) : Prop :=
  parameters.exponentDenominator ≠ 0 ∧
    Nat.Coprime parameters.exponentNumerator
      parameters.exponentDenominator ∧
    Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => model.causticYReadout θ - parameters.uReadout)
      (fun θ =>
        parameters.vScaleReadout *
          Real.rpow |model.causticXReadout θ|
            ((parameters.exponentNumerator : ℝ) /
              (parameters.exponentDenominator : ℝ)))

/--
As `Δθ → 0`, every fixed nonzero `θ` eventually satisfies the source
hierarchy `|Δθ| < |θ|`, the precise local content needed from `Δθ ≪ θ`.
-/
theorem deltaThetaEventuallySmallerThanTheta (θ : ℝ) (hθ : θ ≠ 0) :
    ∀ᶠ Δθ in 𝓝 (0 : ℝ), |Δθ| < |θ| := by
  sorry

/--
IPhO 2026 problem 2, part C.4.

The C.3 caustic has offset `u = R/2`, coefficient
`v = (3/4) R^(1/3)`, and reduced exponent `p/q = 2/3`.
-/
theorem smallAngleCausticPowerLaw (model : Figure2gCausticModel) :
    HasSmallAnglePowerLaw model
      { uReadout := model.frame.radiusReadout / 2
        vScaleReadout :=
          ((3 : ℝ) / 4) *
            Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3)
        exponentNumerator := 2
        exponentDenominator := 3 } := by
  sorry

end
end IPhO2026_2_C_4
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
Determine u, v, and the integers p,q.

\paragraph{Current subquestion.}
For theta << 1, put the caustic in the form Y\_c = v*|X\_c|\textasciicircum{}(p/q) + u. Determine u, v, and the integers p,q.

\paragraph{Recorded answer/context.}
u = R/2, v = (3/4)*R\textasciicircum{}(1/3), p = 2, and q = 3.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T2\_page-4.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.3. Question: Find the limiting intersection coordinates (X\_c,Y\_c) of the neighboring reflected rays. Reusable conclusions: X\_c = R*sin(theta)\textasciicircum{}3; Y\_c = (R/2)*cos(theta)*(2 - cos(2*theta)). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_2\_C\_4.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_2_C_4:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_4.lean.md`
```markdown
on`
  supplies a unit direction but not the source's line/envelope data. The local
  equation-bearing interfaces are therefore the smaller faithful carriers.
- LeanExplore did not return a declaration stating the exact composite
  second-order asymptotic for
  `cos θ * (2 - cos (2θ))`. `Real.cos_bound` and the general Taylor theorem
  supply adequate grounded ingredients, so this is not a statement-layer
  blocker.
- `WithDim Dimension.L𝓭 ℝ` was inspected but not used for the scalar
  coordinate readouts: the requested fractional power coefficient has
  dimension `length^(1/3)`, while the contract is explicitly about numerical
  readouts in one fixed `LengthUnit`. This preserves the physical role without
  inventing unsupported fractional-dimension operations.
- `archon dag-query` was unavailable on this lane's `PATH`. The only
  prerequisite named by the source is C.3, and it was restated locally per the
  explicit natural-language-only dependency policy.

## Redraft requests

- The blueprint target environment has no `\lean{...}` declaration
  association. Synchronization/review should attach the main theorem name
  above. No change to the informal physics statement is requested.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_4.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 14. `IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 17.119
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_1.md`

### Lean excerpt
```lean
implicitly.
-/
structure DenseInsulatedWinding where
  turnCount : ℕ
  currentMagnitude : ElectricCurrentMagnitude
  turnCount_pos : 0 < turnCount
  currentMagnitude_nonneg : 0 ≤ siValue currentMagnitude

/--
The approximately uniform magnitudes of `H`, `B`, and `M` in the torus.
For the isotropic paramagnet, the nonnegative scalar `magnetization` is the
component along the same toroidal direction as `fieldStrength`.
-/
structure UniformToroidalMagneticState where
  fieldStrength : MagneticFieldStrengthMagnitude
  fluxDensity : MagneticFluxDensityMagnitude
  magnetization : MagneticFieldStrengthMagnitude
  fieldStrength_nonneg : 0 ≤ siValue fieldStrength
  fluxDensity_nonneg : 0 ≤ siValue fluxDensity
  magnetization_nonneg : 0 ≤ siValue magnetization

/-- The length `2πR` of the circular Ampèrian loop through the torus. -/
def meanLoopLengthSI (torus : HomogeneousIsotropicParamagneticTorus) : ℝ :=
  2 * Real.pi * siValue torus.meanRadius

/--
The scalar consequence of `B = μ₀ H + μ₀ M` for the common toroidal direction.
It is recorded as a governing law, not as a definition of any field.
-/
def ParamagneticConstitutiveLaw
    (state : UniformToroidalMagneticState)
    (vacuumPermeability : MagneticPermeabilityMagnitude) : Prop :=
  siValue state.fluxDensity =
    siValue vacuumPermeability * siValue state.fieldStrength +
      siValue vacuumPermeability * siValue state.magnetization

/--
Ampère's circuital law reduced using the approximately uniform toroidal field:
the circulation `H (2πR)` equals the enclosed free current `N I`.
-/
def ToroidalAmpereLaw
    (torus : HomogeneousIsotropicParamagneticTorus)
    (winding : DenseInsulatedWinding)
    (state : UniformToroidalMagneticState) : Prop :=
  siValue state.fieldStrength * meanLoopLengthSI torus =
    (winding.turnCount : ℝ) * siValue winding.currentMagnitude

/--
For the Fig. 3a paramagnetic torus, Ampère's law and
`V = (2πR) A` give `H = N I A / V`.
-/
theorem fieldStrength_eq_turns_current_area_div_volume
    (torus : HomogeneousIsotropicParamagneticTorus)
    (winding : DenseInsulatedWinding)
    (state : UniformToroidalMagneticState)
    (vacuumPermeability : MagneticPermeabilityMagnitude)
    (_vacuumPermeability_pos : 0 < siValue vacuumPermeability)
    (_constitutiveLaw : ParamagneticConstitutiveLaw state vacuumPermeability)
    (_ampereLaw : ToroidalAmpereLaw torus winding state) :
    siValue state.fieldStrength =
      (winding.turnCount : ℝ) * siValue winding.currentMagnitude *
        siValue torus.crossSectionArea / siValue torus.volume := by
  sorry

end IPhO2026Problems.IPhO2026_3_A_1
... [leading content omitted]
```

### Blueprint excerpt
```tex
ogeneous isotropic paramagnetic torus has mean radius R, inner radius r
with r << R, volume V, and cross-sectional area A.  An insulated conducting
wire is wound densely around it with N turns and instantaneous current I.
Fields H and B and magnetization M are approximately uniform in the torus.
Use B = mu\_0*H + mu\_0*M, Ampere's law, and the sign convention that work and
heat entering the paramagnetic torus are positive.

Current subquestion:
Write the field magnitude H inside the torus in terms of N, I, A, and V.

\paragraph{Current subquestion.}
Write the field magnitude H inside the torus in terms of N, I, A, and V.

\paragraph{Recorded answer/context.}
H = N*I*A/V.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-2.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_A\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_A_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_A_1.lean.md`
```markdown
ful equation-bearing local abstraction because
  no matching toroidal Ampère-law API was found.
- `ParamagneticConstitutiveLaw` preserves the source material relation as an
  equation-bearing predicate.

## Grounding gaps

- No ready-made Physlib declaration for Ampère's circuital law specialized to a
  uniformly wound paramagnetic torus was found. The local reduced law exposes
  the exact source equation needed by later proofs.
- Physlib's `Electromagnetism.MagneticField` models a spacetime vector field
  `B`; it does not directly provide a dimension-tagged uniform magnetic field
  strength `H` or magnetization `M`.
- The qualitative relation `r ≪ R` has no numerical tolerance in the source.
  It is therefore represented by an explicit dimensionless bound parameter
  rather than an invented fixed constant.

## Verification

- `lean_diagnostic_messages`: only the expected `declaration uses sorry`
  warning.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`: exit code 0
  with only the expected `sorry` warning.
- An in-memory replacement proof closed using the declared assumptions; the
  checked-in theorem body remains `sorry` as required for the autoformalize
  stage.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 15. `IPhO2026Problems/problem_IPhO_2026_3_A_2.lean`

- Compile status: passed
- Open sorries: 2
- Direct-check seconds: 16.451
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_A_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_2.md`

### Lean excerpt
```lean
in Part A.2.

The three governing equations separate the dense-winding flux law, Faraday's
law with the external-source polarity, and the electrical work law.  Thus the
requested closed form is not assumed.  The zero wire-heating equation records
the negligible-resistance approximation from the apparatus description.
-/
structure InfinitesimalMagneticChange
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (_state : UniformParamagneticState geometry winding) where
  fluxDensityChange : WithDim magneticFluxDensityDimension ℝ
  fluxChangePerTurn : WithDim magneticFluxDimension ℝ
  fluxLinkageChange : WithDim magneticFluxDimension ℝ
  externalVoltageTimeIntegral : WithDim magneticFluxDimension ℝ
  sourceWork : SignedEnergyTransfer
  torusHeat : SignedEnergyTransfer
  wireJouleHeat : WithDim energyDimension ℝ
  positiveFluxOrientation : ToroidalOrientation
  orientation_agrees_with_winding :
    positiveFluxOrientation = winding.positiveOrientation
  fluxPerTurnLaw :
    fluxChangePerTurn.val =
      geometry.crossSectionArea.val * fluxDensityChange.val
  denseWindingFluxLinkageLaw :
    fluxLinkageChange.val =
      (winding.turns : ℝ) * fluxChangePerTurn.val
  externalSourceFaradayLaw :
    externalVoltageTimeIntegral.val = fluxLinkageChange.val
  sourcePowerWorkLaw :
    sourceWork.amount.val =
      winding.current.val * externalVoltageTimeIntegral.val
  negligibleWireHeating :
    wireJouleHeat.val = 0

/-- Faraday's law and the electrical work law give the intermediate expression
`dW_emf = I N A dB`, before using the result of Part A.1. -/
lemma source_work_eq_current_turns_area_dB
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (state : UniformParamagneticState geometry winding)
    (change : InfinitesimalMagneticChange geometry winding state) :
    change.sourceWork.amount.val =
      winding.current.val * (winding.turns : ℝ) *
        geometry.crossSectionArea.val * change.fluxDensityChange.val := by
  sorry

/-- **IPhO 2026 Problem 3 A.2.**

For the positive-entering energy convention, the infinitesimal work performed
by the external voltage source is `dW_emf = V H dB`.
-/
theorem external_source_work_for_flux_density_change
    (geometry : ThinToroidalGeometry)
    (winding : IdealToroidalWinding)
    (state : UniformParamagneticState geometry winding)
    (change : InfinitesimalMagneticChange geometry winding state) :
    change.sourceWork.amount.val =
      geometry.volume.val * state.fieldStrength.val *
        change.fluxDensityChange.val := by
  sorry

end IPhO2026Problems.Problem3A2
... [leading content omitted]
```

### Blueprint excerpt
```tex
M, Ampere's law, and the sign convention that work and
heat entering the paramagnetic torus are positive.

Current subquestion:
Find the work dW\_emf performed by the external voltage source when B changes by dB.

\paragraph{Current subquestion.}
Find the work dW\_emf performed by the external voltage source when B changes by dB.

\paragraph{Recorded answer/context.}
dW\_emf = V*H*dB.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-2.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source A.1. Question: Write the field magnitude H inside the torus in terms of N, I, A, and V. Reusable conclusions: H = N*I*A/V. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_A\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_A_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_A_2.lean.md`
```markdown
gnetic dimensions not already exposed as the needed scalar types
  were built compositionally from Physlib base dimensions.
- `ThinToroidalGeometry` preserves the labelled apparatus geometry and the
  small-radius approximation rather than replacing them with unrelated reals.
- `UniformParamagneticState` preserves the distinct physical roles of `H`,
  `B`, `M`, and `μ₀`, with dimension tags and explicit material/Ampère laws.
- `InfinitesimalMagneticChange` preserves the physical derivation by exposing
  flux, linkage, voltage-time, work, heat, and wire-loss quantities separately.
- The local Faraday and power laws are mathematical equations with reusable
  consequences, not opaque predicates.

## Grounding gaps

- LeanExplore found no lumped-circuit Physlib API for Faraday's law, flux
  linkage of a dense `N`-turn winding, or external-source electrical work.
  Faithful local equation fields were introduced instead.
- The `archon` DAG navigation executable advertised in the task prompt was not
  available on this runtime's `PATH`; this did not block the formalization
  because A.1's exact reusable conclusion was present in the blueprint/source
  report.

## Redraft requests

- None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_2.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 16. `IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 11.438
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_A_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_3.md`

### Lean excerpt
```lean
:
    siValue data.fieldStrengthH *
        (2 * Real.pi * siValue data.meanRadiusR) =
      (data.turnCountN : ℝ) * siValue data.currentI
  /-- Static constitutive law `B = μ₀ (H + M)`. -/
  constitutiveLaw :
    siValue data.fluxDensityB =
      siValue data.vacuumPermeabilityMu0 *
        (siValue data.fieldStrengthH + siValue data.magnetizationM)
  /-- Differential constitutive law `dB = μ₀ (dH + dM)`. -/
  differentialConstitutiveLaw :
    siValue changes.dB =
      siValue data.vacuumPermeabilityMu0 *
        (siValue changes.dH + siValue changes.dM)
  /-- For the comparison vacuum core, `dB_vac = μ₀ dH`. -/
  vacuumCoreIncrementLaw :
    siValue changes.dBVac =
      siValue data.vacuumPermeabilityMu0 * siValue changes.dH
  /--
  Reusable conclusion of A.2, included directly rather than imported from
  another problem file: `dW_emf = V H dB`.
  -/
  previousPartSourceWork :
    siValue works.sourceWorkdWemf =
      siValue data.volumeV * siValue data.fieldStrengthH *
        siValue changes.dB
  /-- The same source-work law applied to the vacuum-core comparison. -/
  vacuumCoreWorkLaw :
    siValue works.vacuumCoreWorkdWvac =
      siValue data.volumeV * siValue data.fieldStrengthH *
        siValue changes.dBVac
  /-- The voltage-source work is divided into vacuum and material work. -/
  sourceWorkSplit :
    siValue works.sourceWorkdWemf =
      siValue works.vacuumCoreWorkdWvac +
        siValue works.materialWorkdW
  /-- The wire resistance is negligible, so its Joule-heating work vanishes. -/
  negligibleWireHeating :
    siValue works.wireHeatingWork = 0

/-! ## A.3 target and its SI bridge -/

/--
Scalar bridge for the A.3 subtraction: the material-work value in joules is
`μ₀ V H dM`.
-/
theorem materialWork_siValue_eq
    (data : TorusData) (changes : FieldIncrements) (works : WorkIncrements)
    (laws : Assumptions data changes works) :
    siValue works.materialWorkdW =
      siValue data.vacuumPermeabilityMu0 *
        siValue data.volumeV *
        siValue data.fieldStrengthH *
        siValue changes.dM := by
  sorry

/--
After subtracting the vacuum-core contribution, the work done on the
paramagnetic material is `dW = μ₀ V H dM`.
-/
theorem materialWork_eq_mu0_volume_H_dM
    (data : TorusData) (changes : FieldIncrements) (works : WorkIncrements)
    (laws : Assumptions data changes works) :
    works.materialWorkdW =
      energyFromSI
        (siValue data.vacuumPermeabilityMu0 *
          siValue data.volumeV *
          siValue data.fieldStrengthH *
          siValue changes.dM) := by
  sorry

end Problem3A3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
on that work and
heat entering the paramagnetic torus are positive.

Current subquestion:
Subtract the vacuum-core contribution and write the work dW done on the paramagnetic material.

\paragraph{Current subquestion.}
Subtract the vacuum-core contribution and write the work dW done on the paramagnetic material.

\paragraph{Recorded answer/context.}
dW = mu\_0*V*H*dM.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-2.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source A.2. Question: Find the work dW\_emf performed by the external voltage source when B changes by dB. Reusable conclusions: dW\_emf = V*H*dB. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_A\_3.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_A_3:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_A_3.lean.md`
```markdown
xposes every
  physical consequence needed by a later proof as an equation or inequality.

## Grounding gaps

- No Physlib API was located for a homogeneous isotropic paramagnetic torus,
  magnetization, magnetic field strength `H`, or vacuum-core work
  subtraction. These roles are represented locally with Physlib dimensions
  and explicit governing equations.
- `Electromagnetism.MagneticField` models a spacetime-to-vector map and does
  not directly represent the source's uniform toroidal scalar magnitude.
- Physlib's ready-made `DimArea` uses a nonnegative scalar carrier, while this
  file uses a uniform real-valued dimensionful carrier plus explicit
  positivity for all setup quantities.
- The `archon` executable was unavailable on this lane's `PATH`, so
  `dag-query` could not be run. The blueprint itself marks A.2 as a
  natural-language-only prerequisite, which is restated locally without a
  sibling import.

## Redraft requests

- The blueprint target currently has no `\lean{...}` declaration annotation.
  The plan/review or synchronization step should associate it with
  `IPhO2026Problems.Problem3A3.materialWork_eq_mu0_volume_H_dM`.
- No source-physics redraft is required.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_3.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 17. `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 12.226
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_B_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_1.md`

### Lean excerpt
```lean
amagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s,
      process.magnetizationRateAmperePerMetre s =
        torus.amountMoles * torus.materialK_SI *
            (finalFieldStrength - initialFieldStrength) /
          ((fixedTemperature : ℝ) * torus.volumeCubicMetres) := by
  sorry

/-- Combining the first law, isothermal internal-energy law, equation of
state, and magnetic work law determines the instantaneous heat rate. -/
theorem heatRate_eq
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s,
      process.heatRateJoules s =
        -(vacuumPermeability_SI * torus.amountMoles *
            torus.materialK_SI / (fixedTemperature : ℝ)) *
          process.fieldStrengthAmperePerMetre s *
          (finalFieldStrength - initialFieldStrength) := by
  sorry

/-- The heat transferred into the paramagnetic torus when the magnitude of
`H` changes isothermally from `H_i` to `H_f`.

The sweep parametrization records the orientation, so the same signed formula
also covers a decreasing field magnitude.
-/
theorem heat_transferred_into_torus
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (vacuumPermeability_pos : 0 < vacuumPermeability_SI)
    (temperature_pos : 0 < (fixedTemperature : ℝ))
    (initialFieldStrength_nonneg : 0 ≤ initialFieldStrength)
    (finalFieldStrength_nonneg : 0 ≤ finalFieldStrength)
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    netHeatEnteringInJoules process =
      -(vacuumPermeability_SI * torus.amountMoles *
          torus.materialK_SI / (2 * (fixedTemperature : ℝ))) *
        (finalFieldStrength ^ 2 - initialFieldStrength ^ 2) := by
  sorry

end

end ProblemIPhO2026_3_B_1
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
rent subquestion:
At fixed temperature T, H changes from H\_i to H\_f. Find the heat Q transferred into the torus.

\paragraph{Current subquestion.}
At fixed temperature T, H changes from H\_i to H\_f. Find the heat Q transferred into the torus.

\paragraph{Recorded answer/context.}
Q = -(mu\_0*n*K/(2*T))*(H\_f\textasciicircum{}2 - H\_i\textasciicircum{}2).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source A.3. Question: Subtract the vacuum-core contribution and write the work dW done on the paramagnetic material. Reusable conclusions: dW = mu\_0*V*H*dM. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_B\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_B_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_B_1.lean.md`
```markdown
and their sign constraints.
- `IsothermalFieldSweep` preserves temperature, field and magnetization
  magnitudes, heat capacity, dimensionful energy curves, and explicit
  derivative readouts.
- `SatisfiesIsothermalParamagneticTorusLaws` exposes every physical law as a
  usable equation or derivative statement.
- `netHeatEnteringInJoules` names the signed finite heat entering the torus as
  an endpoint energy difference; it does not encode the answer.

These abstractions use real numbers only for explicitly named SI-coordinate
readouts and measured scalar magnitudes. They do not replace energy or
temperature with transparent scalar aliases.

## Grounding gaps

- Physlib provides no directly matching paramagnetic-torus process interface,
  scalar magnetic-field-strength magnitude type, magnetization-magnitude type,
  or constant-magnetization heat-capacity law found by the searches above.
  The local readout and governing-law interfaces faithfully cover those gaps.
- `Electromagnetism.MagneticField` and
  `CanonicalEnsemble.heatCapacity` are semantically incompatible near misses,
  so they were not forced into the model.
- No bridge is blocked and no blueprint redraft is requested.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 18. `IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 17.35
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_B_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_2.md`

### Lean excerpt
```lean
atureSI s).val
        * derivWithin (fun u => (path.fieldStrengthMagnitudeSI u).val)
            processDomain s := by
  sorry

/-- The positive energy-times-temperature scale occurring in the ODE. -/
def magnetothermalScaleSI
    (model : ParamagneticTorusModel) (path : AdiabaticPathReadout) (s : ℝ) : ℝ :=
  model.heatCapacityParameterSI.val
    + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
      * (path.fieldStrengthMagnitudeSI s).val ^ 2

/-- The path invariant obtained by separating the reduced ODE. -/
noncomputable def magnetothermalInvariantSI
    (model : ParamagneticTorusModel) (path : AdiabaticPathReadout) (s : ℝ) : ℝ :=
  (path.temperatureSI s).val ^ 2 / magnetothermalScaleSI model path s

/--
Along any admissible adiabatic path, `T² / (λ + μ₀ K H²)` is constant.
Mathlib's derivative-zero-on-an-interval theorem can carry the final
calculus step once the reduced ODE has been established.
-/
theorem magnetothermal_invariant_constant
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength) :
    ∀ s ∈ processDomain,
      magnetothermalInvariantSI model path s =
        magnetothermalInvariantSI model path 0 := by
  sorry

/-! ## Current subquestion -/

/--
For an adiabatic change from `Hᵢ` to `H_f`, the requested temperature change
`ΔT = T_f - Tᵢ`.

The positivity assumptions in the physical model and along the path select the
positive square-root branch.
-/
theorem adiabatic_temperature_change
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength) :
    finalTemperature.val - initialTemperature.val =
      initialTemperature.val *
        (Real.sqrt
            ((model.heatCapacityParameterSI.val
                + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
                  * finalFieldStrength.val ^ 2) /
              (model.heatCapacityParameterSI.val
                + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
                  * initialFieldStrength.val ^ 2)) - 1) := by
  sorry

end IPhO2026Problems.IPhO2026_3_B_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
r an adiabatic change H\_i -> H\_f starting at T\_i, determine Delta T = T\_f - T\_i.

\paragraph{Current subquestion.}
For an adiabatic change H\_i -> H\_f starting at T\_i, determine Delta T = T\_f - T\_i.

\paragraph{Recorded answer/context.}
Delta T = T\_i*[sqrt((lambda + mu\_0*K*H\_f\textasciicircum{}2)/(lambda + mu\_0*K*H\_i\textasciicircum{}2)) - 1].

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source A.3. Question: Subtract the vacuum-core contribution and write the work dW done on the paramagnetic material. Reusable conclusions: dW = mu\_0*V*H*dM. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_B\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_B_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_B_2.lean.md`
```markdown
erning laws; neither encodes the
  current target.

## Grounding gaps

- Physlib has dimension-tagged quantities but no located ready-made API for
  this lumped paramagnetic-torus equation of state, heat-capacity law,
  first-law sign convention, or magnetic-work path law. These are therefore
  represented locally by explicit real equations on dimension-tagged
  readouts.
- `Physlib.Dimension` has no amount-of-substance base dimension. The model
  preserves `n` as a named molar scalar readout and documents how `K` and `λ`
  carry the remaining dimensions.
- `WithDim` records dimension but not a chosen unit system in its type. The
  process contract consistently interprets `.val` fields as one coherent SI
  readout system; no cross-unit conversion occurs inside the theorem.
- The `archon dag-query` helper advertised by the task prompt was not available
  on `PATH` in this lane. This did not block the independent formalization, and
  no sibling Lean output was imported.

## Verification

- LSP diagnostics: success, with only three `sorry` warnings.
- Shell check:
  `lake env lean IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`
  exits successfully with exactly the same three warnings.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_2.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 19. `IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`

- Compile status: passed
- Open sorries: 2
- Direct-check seconds: 11.032
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_2.md`

### Lean excerpt
```lean
equations preserve the orientation and sign convention from part
B.1: heat transferred *into* the torus is positive. Thus `Q_c` is used on
`2 → 3`, while the signed heat into the torus on `4 → 1` is `-Q_h`.
-/
structure SatisfiesParamagneticCarnotLaws (cycle : CarnotCycleData) : Prop where
  /-- Equation of state `T M V = n K H` at every vertex. -/
  equationOfState : ∀ v : CycleVertex,
    stateTemperatureSI cycle v * magnetizationSI cycle v *
        siValue cycle.torus.volume =
      cycle.torus.constituentCount * siValue cycle.torus.curieConstant *
        magneticFieldSI cycle v
  /--
  The isothermal heat law on `2 → 3`, where `Q_c` is absorbed by the torus.
  -/
  coldIsothermalHeat :
    siValue cycle.heatFromCold =
      -(siValue cycle.torus.vacuumPermeability *
          cycle.torus.constituentCount * siValue cycle.torus.curieConstant /
          (2 * siValue cycle.coldTemperature)) *
        (magneticFieldSI cycle .three ^ 2 - magneticFieldSI cycle .two ^ 2)
  /--
  The isothermal heat law on `4 → 1`; signed heat into the torus is `-Q_h`.
  -/
  hotIsothermalHeat :
    -(siValue cycle.heatToHot) =
      -(siValue cycle.torus.vacuumPermeability *
          cycle.torus.constituentCount * siValue cycle.torus.curieConstant /
          (2 * siValue cycle.hotTemperature)) *
        (magneticFieldSI cycle .one ^ 2 - magneticFieldSI cycle .four ^ 2)
  /--
  Entropy balance for a reversible Carnot cycle:
  `Q_h / T_h = Q_c / T_c`.
  -/
  carnotEntropyBalance :
    siValue cycle.heatToHot / siValue cycle.hotTemperature =
      siValue cycle.heatFromCold / siValue cycle.coldTemperature

/-! ## Derived relations requested by part C.2 -/

/--
The algebraic square balance obtained by combining the equation of state, the
two isothermal heat equations, and the reversible Carnot heat balance.
-/
theorem magnetization_square_balance
    (cycle : CarnotCycleData)
    (laws : SatisfiesParamagneticCarnotLaws cycle) :
    magnetizationSI cycle .one ^ 2 - magnetizationSI cycle .four ^ 2 =
      magnetizationSI cycle .two ^ 2 - magnetizationSI cycle .three ^ 2 := by
  sorry

/--
IPhO 2026 problem 3 C.2: the magnetization at state `1`, on the nonnegative
magnitude branch, in terms of the magnetizations at states `2`, `3`, and `4`.
-/
theorem magnetization_at_state_one
    (cycle : CarnotCycleData)
    (laws : SatisfiesParamagneticCarnotLaws cycle) :
    magnetizationSI cycle .one =
      Real.sqrt
        (magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2 +
          magnetizationSI cycle .four ^ 2) := by
  sorry

end

end IPhO2026Problem3C2
... [leading content omitted]
```

### Blueprint excerpt
```tex
roposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.1. Question: At fixed temperature T, H changes from H\_i to H\_f. Find the heat Q transferred into the torus. Reusable conclusions: Q = -(mu\_0*n*K/(2*T))*(H\_f\textasciicircum{}2 - H\_i\textasciicircum{}2). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\item Source C.1. Question: Label T\_h and T\_c on Figure 3b and identify the processes on which Q\_h and Q\_c are transferred. Reusable conclusions: States 1 and 4 lie at T\_h; states 2 and 3 lie at T\_c. Q\_c is absorbed on 2->3, and Q\_h is delivered on 4->1. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_C\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_C_2:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_2.lean.md`
```markdown
ess kinds.
- The three data structures preserve the distinction between a physical
  dimensionful quantity and its real SI readout.
- `SatisfiesParamagneticCarnotLaws` supplies the smallest explicit local
  governing-law interface found sufficient for the derivation.

## Grounding gaps

- LeanExplore exposed a general Physlib dimension system but no ready-made
  magnetization-magnitude, paramagnetic equation-of-state, isothermal magnetic
  heat, or reversible Carnot refrigerator API. These are represented locally
  by dimension-tagged quantities and explicit equations rather than guessed
  library names.
- The `archon dag-query` navigation command was unavailable on this prover
  process's `PATH`; the blueprint itself specifies that previous parts are
  natural-language prerequisites only, so no sibling Lean dependency was
  introduced.
- No formalization redraft is requested.

## Verification

- LSP diagnostics: no errors; exactly two expected `declaration uses sorry`
  warnings, for the two derived theorems.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`: exit code
  `0`, with the same two expected warnings.
- Project-default `lake build`: completed successfully.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_2.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 20. `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 17.677
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_3.md`

### Lean excerpt
```lean
uumPermeability.siValue *
          setup.torus.amount.siValue *
          setup.torus.curieConstant.siValue /
          (2 * (cycle.state .two).temperature.siValue)) *
        ((cycle.state .three).fieldStrength.siValue ^ 2 -
          (cycle.state .two).fieldStrength.siValue ^ 2)
  hotHeatEquation :
    heats.deliveredToHot.siValue =
      (setup.vacuumPermeability.siValue *
          setup.torus.amount.siValue *
          setup.torus.curieConstant.siValue /
          (2 * (cycle.state .one).temperature.siValue)) *
        ((cycle.state .one).fieldStrength.siValue ^ 2 -
          (cycle.state .four).fieldStrength.siValue ^ 2)

/-- Constant-density, constant-specific-heat calorimetry for the helium.

The energy absorbed by the torus is removed from the helium.  The inequality
selects the cooling rather than heating orientation of the signed balance.
-/
structure HeliumCalorimetryLaw
    (setup : RefrigerationSetup) (heats : CycleHeatExchange)
    (finalTemperature : SIQuantity .temperature) : Prop where
  energyBalance :
    heats.absorbedFromCold.siValue =
      setup.helium.density.siValue *
        setup.helium.volume.siValue *
        setup.helium.specificHeatCapacity.siValue *
        (setup.helium.initialTemperature.siValue - finalTemperature.siValue)
  coolingOrientation :
    finalTemperature.siValue ≤ setup.helium.initialTemperature.siValue

/-- After one cycle, the torus absorbs approximately `0.129 J`; the helium
cools by approximately `0.00992 K`, to approximately `0.99008 K`.

The bounds are numerical-rounding envelopes around the values reported in the
official answer, rather than measurement-uncertainty assumptions.
-/
theorem IPhO_2026_3_C_3_helium_temperature_after_one_cycle
    (setup : RefrigerationSetup)
    (cycle : CarnotTorusCycle)
    (heats : CycleHeatExchange)
    (finalTemperature : SIQuantity .temperature)
    (readouts : SuppliedReadouts setup cycle)
    (volumeLaw : TorusVolumeMassBalance setup)
    (equationOfState : ParamagneticEquationOfState setup cycle)
    (temperaturePattern : CarnotTemperaturePattern cycle)
    (previousPartC2 : PreviousPartC2MagnetizationRelation cycle)
    (heatLaw : CarnotIsothermalHeatLaw setup cycle heats)
    (calorimetry : HeliumCalorimetryLaw setup heats finalTemperature) :
    abs (heats.absorbedFromCold.siValue - 129 / 1000) ≤ 1 / 2000 ∧
      abs
          ((setup.helium.initialTemperature.siValue - finalTemperature.siValue) -
            992 / 100000) ≤
        1 / 20000 ∧
      abs (finalTemperature.siValue - 99008 / 100000) ≤ 1 / 20000 := by
  sorry

end Problem3C3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
K.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-4.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.1. Question: At fixed temperature T, H changes from H\_i to H\_f. Find the heat Q transferred into the torus. Reusable conclusions: Q = -(mu\_0*n*K/(2*T))*(H\_f\textasciicircum{}2 - H\_i\textasciicircum{}2). Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\item Source C.2. Question: Express M\_1 in terms of M\_2, M\_3, and M\_4. Reusable conclusions: M\_1 = sqrt(M\_2\textasciicircum{}2 - M\_3\textasciicircum{}2 + M\_4\textasciicircum{}2), taking the nonnegative magnitude. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_C\_3.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_C_3:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_3.lean.md`
```markdown
uantity` combines a dimension-tagged Physlib value with nonnegativity,
  faithfully representing the magnitude readouts in the source rather than
  collapsing physical primitives to transparent real aliases.
- Mole is not a Physlib foundational dimension. The role index therefore
  preserves `mol`, `kg/mol`, and `K·m³/mol` meanings while the dimensional
  component uses Physlib's available five-base-dimension system.
- The torus, helium, cycle, heat, equation-of-state, isothermal-heat, and
  calorimetry interfaces are local because no single matching
  Physlib/Mathlib API was found. Each exposes the source equations and
  inequalities needed for later proofs.

## Grounding gaps

- Physlib's `Dimension` does not include amount of substance, so mole cannot
  be represented as a sixth foundational exponent. The local role index
  preserves that semantic distinction without inventing a library name.
- LeanExplore found no ready-made scalar API for this lumped paramagnetic
  Carnot torus, the B.1 magnetic isothermal heat law, or the helium
  calorimetry coupling. Faithful local equation-bearing interfaces were used.
- No derivability bridge remains blocked.

## Redraft requests

- None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_3.md`
```markdown
e Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 21. `IPhO2026Problems/problem_IPhO_2026_3_C_4.lean`

- Compile status: passed
- Open sorries: 2
- Direct-check seconds: 9.618
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_4.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_4.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_4.md`

### Lean excerpt
```lean
_run : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.temperatureTrajectory τ).val
  temperature_lt_hot_on_run : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.temperatureTrajectory τ).val <
      experiment.hotReservoirTemperature.val
  coldHeatAbsorptionRate_pos : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.coldHeatAbsorptionRate τ).val
  hotHeatDeliveryRate_pos : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    0 < (process.hotHeatDeliveryRate τ).val
  carnot_heat_ratio : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.coldHeatAbsorptionRate τ).val /
        (process.hotHeatDeliveryRate τ).val =
      (process.temperatureTrajectory τ).val /
        experiment.hotReservoirTemperature.val
  body_heat_balance : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.coldHeatAbsorptionRate τ).val =
      -experiment.heatCapacity.val *
        deriv (fun s => (process.temperatureTrajectory s).val) τ
  refrigerator_power_balance : ∀ τ ∈ Set.Icc 0 experiment.elapsedTime.val,
    (process.hotHeatDeliveryRate τ).val -
        (process.coldHeatAbsorptionRate τ).val =
      experiment.inputPower.val

/--
Eliminating the cold- and hot-side heat rates gives the instantaneous cooling
equation that will be integrated in `elapsed_time_formula`.
-/
theorem instantaneous_cooling_power_equation
    (experiment : CarnotCoolingExperiment)
    (process : CarnotCoolingProcess)
    (law : SatisfiesCarnotCoolingLaw experiment process)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 experiment.elapsedTime.val) :
    experiment.inputPower.val =
      experiment.heatCapacity.val *
        (experiment.hotReservoirTemperature.val /
          (process.temperatureTrajectory τ).val - 1) *
        (-deriv (fun s => (process.temperatureTrajectory s).val) τ) := by
  sorry

/--
The required running time for cooling the body from `T₀` to `T` with constant
heat capacity, constant refrigerator input power, and constant hot-reservoir
temperature.
-/
theorem elapsed_time_formula
    (experiment : CarnotCoolingExperiment)
    (process : CarnotCoolingProcess)
    (law : SatisfiesCarnotCoolingLaw experiment process) :
    experiment.elapsedTime.val =
      (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
        experiment.inputPower.val) *
      (Real.log (experiment.initialTemperature.val /
          experiment.finalTemperature.val) -
        (experiment.initialTemperature.val -
            experiment.finalTemperature.val) /
          experiment.hotReservoirTemperature.val) := by
  sorry

end IPhO2026_3_C_4
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
de of heat
delivered to the hot reservoir and Q\_c is the magnitude absorbed from the cold
reservoir.  The equation of state is T*M*V = n*K*H and the isothermal heat
relation from part B may be reused.

Current subquestion:
A body of heat capacity C\_c is cooled from T\_0 to T while refrigerator input power P and hot-reservoir temperature T\_h remain constant. Determine the elapsed time.

\paragraph{Current subquestion.}
A body of heat capacity C\_c is cooled from T\_0 to T while refrigerator input power P and hot-reservoir temperature T\_h remain constant. Determine the elapsed time.

\paragraph{Recorded answer/context.}
t = (C\_c*T\_h/P)*[ln(T\_0/T) - (T\_0 - T)/T\_h].

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-4.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_C\_4.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_C_4:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_4.lean.md`
```markdown
quations needed to derive the answer without assuming
  the answer.

Real numbers are used only as readouts in a fixed coherent unit convention,
for time coordinates of those readouts, and for the amount-of-substance and
Curie-constant SI projections unsupported by Physlib's five-base-dimension
type.

## Grounding gaps

- No matching Mathlib/Physlib Carnot-refrigerator interface was found. The
  local law relation therefore exposes the exact source equations directly.
- Physlib's `Dimension` has components for length, time, mass, charge, and
  temperature, but not amount of substance. Consequently
  `amountOfSubstanceMoles` and `curieConstantSI` are explicitly named SI scalar
  readouts rather than falsely dimension-tagged quantities.
- The `archon dag-query` executable was unavailable on this lane's `PATH`, so
  the read-only dependency graph could not be queried. The source report lists
  no previous-part Lean dependencies, and no sibling module was imported.
- Blueprint redraft request: add
  `\lean{IPhO2026Problems.IPhO2026_3_C_4.elapsed_time_formula}` to the target
  theorem environment. The later deterministic synchronization phase, not
  this prover, should manage `\leanok`.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_4.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 22. `IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 10.632
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_5.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_5.md`

### Lean excerpt
```lean
sedTime
  positive_final_temperature :
    0 < temperatureValue run.finalBodyTemperature
  final_below_initial :
    temperatureValue run.finalBodyTemperature <
      temperatureValue run.initialBodyTemperature
  initial_below_hot :
    temperatureValue run.initialBodyTemperature <
      temperatureValue run.finalCycle.hotReservoirTemperature
  final_cycle_at_body_temperature :
    run.finalCycle.coldReservoirTemperature = run.finalBodyTemperature
  heat_removed_from_constant_heat_capacity :
    siValue run.totalHeatAbsorbedFromCold =
      siValue run.bodyHeatCapacity *
        (temperatureValue run.initialBodyTemperature -
          temperatureValue run.finalBodyTemperature)
  work_from_constant_power :
    siValue run.totalWorkInput =
      siValue run.inputPower * siValue run.elapsedTime

/-- The reusable elapsed-time conclusion of part C.4. -/
structure C4ElapsedTimeResult (run : CoolingRun) : Prop where
  elapsed_time :
    siValue run.elapsedTime =
      (siValue run.bodyHeatCapacity *
          temperatureValue run.finalCycle.hotReservoirTemperature /
          siValue run.inputPower) *
        (Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
          (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature) /
            temperatureValue run.finalCycle.hotReservoirTemperature)

/-- The overall coefficient of performance, `Q_c / W`, for the whole run. -/
noncomputable def overallCoefficientOfPerformance (run : CoolingRun) : ℝ :=
  siValue run.totalHeatAbsorbedFromCold / siValue run.totalWorkInput

/-- Blueprint label: `thm:physics:IPhO_2026_3_C_5:target`.

The overall COP for every cycle performed while the body cools from `T₀` to
`T`, using the elapsed time obtained in C.4.
-/
theorem overall_coefficient_of_performance
    (run : CoolingRun)
    (isothermalModel : IsothermalHeatModel)
    (_isothermalLaw :
      IsothermalHeatRelation run.finalCycle isothermalModel)
    (_figureLaws : Figure3bCarnotLaws run.finalCycle isothermalModel)
    (coolingLaws : ConstantPowerCoolingLaws run)
    (c4Result : C4ElapsedTimeResult run) :
    overallCoefficientOfPerformance run =
      (temperatureValue run.finalCycle.hotReservoirTemperature /
          (temperatureValue run.initialBodyTemperature -
            temperatureValue run.finalBodyTemperature) *
          Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
        1)⁻¹ := by
  sorry

end IPhO2026_3_C_5
... [leading content omitted]
```

### Blueprint excerpt
```tex
me found in C4.

\paragraph{Current subquestion.}
Determine the overall coefficient of performance COP = Q\_c/W for all cycles up to the time found in C4.

\paragraph{Recorded answer/context.}
COP = [(T\_h/(T\_0 - T))*ln(T\_0/T) - 1]\textasciicircum{}(-1).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-4.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.4. Question: A body of heat capacity C\_c is cooled from T\_0 to T while refrigerator input power P and hot-reservoir temperature T\_h remain constant. Determine the elapsed time. Reusable conclusions: t = (C\_c*T\_h/P)*[ln(T\_0/T) - (T\_0 - T)/T\_h]. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_3\_C\_5.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_3_C_5:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_5.lean.md`
```markdown
CyclePoint`, `Figure3bCarnotCycle`, `IsothermalHeatModel`, and
  `CoolingRun` preserve the state labels, branch orientation, sign convention,
  per-cycle quantities, and run totals.
- The four law/result structures expose reusable equations and inequalities;
  none is an unconstrained opaque predicate.

## Grounding gaps

- Physlib currently supplies `DimEnergy` but no ready aliases for power,
  duration, heat capacity, volume, or ampere/metre. These were faithfully
  constructed from `Dimensionful`, `WithDim`, and the base dimensions.
- Physlib's dimension basis has no amount-of-substance/mole coordinate.
  Molar amount and Curie-constant values therefore remain explicitly named SI
  scalar readouts inside `ParamagneticTorus`.
- No grounded library API for the specific paramagnetic Carnot cycle,
  isothermal magnetic heat law, or overall refrigerator COP was found. Small
  local structures were introduced with explicit equations rather than opaque
  physics predicates.
- The `archon` DAG command advertised in the task prompt was unavailable on
  this lane's shell `PATH`; no sibling Lean dependency was introduced, in
  accordance with the natural-language-only previous-part policy.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_5.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 23. `IPhO2026Problems/problem_IPhO_2026_4_A_1.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 17.541
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_4_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_A_1.md`

### Lean excerpt
```lean
er r /
    (gasConstantSI * r.temperatureK.upper)

def propagatedAmountUpper (r : ExperimentalInputReadouts) (gasConstantSI : ℝ) : ℝ :=
  r.pressurePa.upper * propagatedVolumeUpper r /
    (gasConstantSI * r.temperatureK.lower)

/-- The propagated inventory interval, including the Avogadro conversion. -/
def InventoryInPropagatedBounds
    (s : ConfinedAirColumnState) (r : ExperimentalInputReadouts)
    (gasConstantSI avogadroPerMole : ℝ) : Prop :=
  propagatedMassLower r ≤ siValue s.mass ∧
  siValue s.mass ≤ propagatedMassUpper r ∧
  propagatedAmountLower r gasConstantSI ≤ s.amount.moles ∧
  s.amount.moles ≤ propagatedAmountUpper r gasConstantSI ∧
  propagatedAmountLower r gasConstantSI * avogadroPerMole ≤
    s.molecules.estimatedCount ∧
  s.molecules.estimatedCount ≤
    propagatedAmountUpper r gasConstantSI * avogadroPerMole

/-- Propagation of the input readout uncertainties to `m`, `n`, and `N`. -/
theorem propagateInventoryUncertainty
    (run : IsochoricApparatusRun)
    (r : ExperimentalInputReadouts)
    (gasConstantSI avogadroPerMole : ℝ)
    (hgeometry : Figure17GeometryLaw run.geometry)
    (hlaws : AirInventoryLaws run.state gasConstantSI avogadroPerMole)
    (hcover : InputReadoutsCover run r)
    (hvalid : ValidInputReadouts r gasConstantSI avogadroPerMole) :
    InventoryInPropagatedBounds run.state r gasConstantSI avogadroPerMole := by
  sorry

/-- The relation asserting agreement with every number in the official sample.

The conversions are `kg → g`, `mol → mmol`, and molecules to units of `10²¹`.
-/
def AgreesWithOfficialSample (s : ConfinedAirColumnState) : Prop :=
  officialSample.massGrams.Covers (1000 * siValue s.mass) ∧
  officialSample.amountMillimoles.Covers (1000 * s.amount.moles) ∧
  officialSample.moleculesInTenTo21.Covers
    (s.molecules.estimatedCount / (10 : ℝ) ^ 21)

/-- Numerical target recorded for A.1 in the supplied source report.

The statement deliberately keeps the result on the conclusion side.  Its proof
requires the numerical Figure 17 dimensions and their error budget, which are
not visible on the supplied source-page image.
-/
theorem officialSampleTarget
    (run : IsochoricApparatusRun)
    (gasConstantSI avogadroPerMole : ℝ)
    (hgeometry : Figure17GeometryLaw run.geometry)
    (hdensity : AmbientDensityReadout run.state)
    (hlaws : AirInventoryLaws run.state gasConstantSI avogadroPerMole)
    (hgas : 0 < gasConstantSI)
    (havogadro : 0 ≤ avogadroPerMole)
    (htemperature : 0 < siValue run.state.temperature) :
    AgreesWithOfficialSample run.state := by
  sorry

end Problem4A1
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
linder.  Propylene glycol is introduced to h = 4.5 cm so the air volume is
fixed.  Use the cylinder dimensions in Figure 17, ambient air density
rho\_a = 1.12 kg/m\textasciicircum{}3, and the ideal-gas law P*V = n*R*T.  The outer-cylinder
water bath is heated while pressure and temperature are recorded.

Current subquestion:
Determine the mass m, amount n, and number N of molecules in the confined air column.

\paragraph{Current subquestion.}
Determine the mass m, amount n, and number N of molecules in the confined air column.

\paragraph{Recorded answer/context.}
Official sample: m = 0.94 +/- 0.02 g, n = 3.24 mmol (reported uncertainty 0.7 mmol), N = (1.95 +/- 0.05)e21.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-9.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_A\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_A_1:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_4_A_1.lean.md`
```markdown
alid physics” tag.

## Grounding gaps

- **Amount/Avogadro API gap:** Physlib has no amount-of-substance base dimension
  or Avogadro constant carrier. Faithful constrained local abstractions are
  used.
- **Ideal-gas API mismatch:** `IdealGas.ideal_gas_law` uses a unitless
  statistical-mechanics model with `R = 1`; it cannot carry this SI experiment.
- **Dependency navigation gap:** the advertised `archon dag-query` executable
  was not on `PATH`; the source report has no previous parts, so this did not
  create a dependency ambiguity.

## Redraft requests

- **Figure/data gap:** provide Figure 17's numerical inner-cylinder dimensions,
  the pressure/temperature or molar-mass data used for A.1, and the associated
  input uncertainties. Without them, `officialSampleTarget` is not derivable.
- **Recorded-answer consistency request:** confirm the decimal places in
  `0.94 g`, `3.24 ± 0.7 mmol`, and the molecule uncertainty. The current amount
  and molecule error bars do not propagate consistently under `N = nN_A`.
- **Blueprint link request:** add the declaration links described above and
  flesh out the informal numerical derivation once the missing Figure 17 data
  are available.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_A_1.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 24. `IPhO2026Problems/problem_IPhO_2026_4_A_5.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 16.426
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_A_5.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_4_A_5.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_A_5.md`

### Lean excerpt
```lean
ure_Pa) * (pressureChange_Pa / temperatureChange_K)

/-- A scalar estimate together with its symmetric reported uncertainty. -/
structure Estimate where
  centralValue : ℝ
  uncertainty : ℝ

/-- Membership in the closed symmetric uncertainty band of an estimate. -/
def Estimate.Contains (estimate : Estimate) (value : ℝ) : Prop :=
  0 ≤ estimate.uncertainty ∧
  |value - estimate.centralValue| ≤ estimate.uncertainty

/-- The official experimental answer `0.0034 ± 0.0007 K⁻¹`. -/
def officialCoefficientEstimatePerKelvin : Estimate where
  centralValue := 0.0034
  uncertainty := 0.0007

/--
The ideal-gas law at fixed positive volume supplies the proportionality used
in the pressure-versus-temperature plot of part A.3.
-/
theorem idealGasLaw_implies_isochoricPressureLinearity
    (run : IsochoricHeatingRun)
    (hPrepared : IsPreparedIsochoricApparatus run.apparatus)
    (hAmount : 0 < run.amountOfAir_mol)
    (hGasConstant : 0 < run.universalGasConstant_J_per_mol_K)
    (hIdealGas : ObeysIsochoricIdealGasLaw run) :
    HasIsochoricPressureLinearity run := by
  sorry

/--
For a positive reference state and a genuinely heated second state, the
normalized secant slope of an isochoric proportionality is `1 / T₀`.
-/
theorem thermalPressureCoefficient_eq_inverse_referenceTemperature
    (run : IsochoricHeatingRun)
    (hReference : UsesStandardReferenceState run)
    (hHeating : IsHeatingBranch run)
    (hLinearity : HasIsochoricPressureLinearity run) :
    thermalPressureCoefficientPerKelvin run =
      1 / temperatureInKelvin run.referenceTemperature := by
  sorry

/--
IPhO 2026 experimental problem 4, part A.5.

The ideal-gas coefficient at the stated reference temperature is `1 / 273.15
K`, lies in the official `0.0034 ± 0.0007 K⁻¹` interval, and rounds to
`0.0037 K⁻¹` at four decimal places.
-/
theorem IPhO2026_4_A_5_thermalPressureCoefficient
    (run : IsochoricHeatingRun)
    (hPrepared : IsPreparedIsochoricApparatus run.apparatus)
    (hReference : UsesStandardReferenceState run)
    (hHeating : IsHeatingBranch run)
    (hAmount : 0 < run.amountOfAir_mol)
    (hGasConstant : 0 < run.universalGasConstant_J_per_mol_K)
    (hIdealGas : ObeysIsochoricIdealGasLaw run) :
    thermalPressureCoefficientPerKelvin run =
        1 / temperatureInKelvin run.referenceTemperature ∧
      thermalPressureCoefficientPerKelvin run = 1 / ((27315 : ℝ) / 100) ∧
      officialCoefficientEstimatePerKelvin.Contains
        (thermalPressureCoefficientPerKelvin run) ∧
      |thermalPressureCoefficientPerKelvin run - 0.0037| ≤ 0.00005 := by
  sorry

end IPhO2026Problems.Problem4A5
... [leading content omitted]
```

### Blueprint excerpt
```tex
ta\_0 = (1/P\_0)*(Delta P/Delta T).

\paragraph{Current subquestion.}
Determine the constant-volume thermal pressure coefficient beta\_0 = (1/P\_0)*(Delta P/Delta T).

\paragraph{Recorded answer/context.}
Official sample: beta\_0 = 0.0034 +/- 0.0007 K\textasciicircum{}(-1); ideal-gas reference 1/273.15 K = 0.0037 K\textasciicircum{}(-1).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-9.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source A.3. Question: Plot pressure as a function of temperature from A2. Reusable conclusions: The expected isochoric ideal-gas plot is linear: P is proportional to absolute T. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_A\_5.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_A_5:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_4_A_5.lean.md`
```markdown
ymbolic parameters; no numerical
  figure data were invented.
- The source provides no A.2 measurement table or raw uncertainty model, so a
  derivation of the reported uncertainty from sensor errors cannot be stated.
  The final reported uncertainty itself is fully preserved.
- Physlib's `IdealGas.ideal_gas_law` is not a signature match for this
  experimental SI model, as described above.
- `archon dag-query` was attempted, but `archon` was not available on this
  lane's `PATH`. The blueprint itself lists only A.3 as a natural-language
  prerequisite, which is represented locally without a sibling import.

## Redraft requests

- If exact Figure 17 numerical geometry is desired in this chapter, add the
  official page containing Figure 17 or transcribe its diameter and height
  values into the source report.
- No theorem-contract redraft is otherwise required.

## Verification

- `mcp__archon_lean_lsp.lean_diagnostic_messages`: no errors; exactly three
  expected `declaration uses sorry` warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_A_5.lean`: exit code 0;
  exactly the same three warnings.
- `archon-protected.yaml` has no active rule affecting the assigned file.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_A_5.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 25. `IPhO2026Problems/problem_IPhO_2026_4_B_4.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 17.509
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_B_4.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_4_B_4.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_B_4.md`

### Lean excerpt
```lean
eight_pos :
    0 < apparatus.measuredState.gasColumnHeight.metreReadout
  referenceCylinderGeometry :
    apparatus.referenceState.gasVolume.cubicMetreReadout =
      apparatus.innerCylinderCrossSection.squareMetreReadout *
        apparatus.referenceState.gasColumnHeight.metreReadout
  measuredCylinderGeometry :
    apparatus.measuredState.gasVolume.cubicMetreReadout =
      apparatus.innerCylinderCrossSection.squareMetreReadout *
        apparatus.measuredState.gasColumnHeight.metreReadout
  referenceDaltonLaw :
    apparatus.referenceState.totalPressure.pascalReadout =
      apparatus.referenceState.dryAirPartialPressure.pascalReadout +
        apparatus.referenceState.waterVaporPartialPressure.pascalReadout
  measuredDaltonLaw :
    apparatus.measuredState.totalPressure.pascalReadout =
      apparatus.measuredState.dryAirPartialPressure.pascalReadout +
        apparatus.measuredState.waterVaporPartialPressure.pascalReadout
  icOcReferencePressureBalance :
    apparatus.referenceState.totalPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout
  icOcMeasuredPressureBalance :
    apparatus.measuredState.totalPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout
  referenceVaporPressureNegligible :
    apparatus.referenceState.waterVaporPartialPressure.pascalReadout = 0
  measuredVaporPressure_nonneg :
    0 ≤ apparatus.measuredState.waterVaporPartialPressure.pascalReadout
  dryAirIdealGasConservation :
    apparatus.referenceState.dryAirPartialPressure.pascalReadout *
          apparatus.referenceState.gasVolume.cubicMetreReadout /
        apparatus.referenceState.temperature.kelvinReadout =
      apparatus.measuredState.dryAirPartialPressure.pascalReadout *
          apparatus.measuredState.gasVolume.cubicMetreReadout /
        apparatus.measuredState.temperature.kelvinReadout

/-- In the Figure 19 idealized pressure-balance model,

`Pᵥ = P_atm * (1 - H₀ * T / (H * T₀))`.

Here every symbol denotes the corresponding SI scalar readout carried by
`apparatus`. -/
theorem vaporPressurePascal_eq
    (apparatus : Figure19Apparatus)
    (h : B4Assumptions apparatus) :
    apparatus.measuredState.waterVaporPartialPressure.pascalReadout =
      apparatus.atmosphericPressure.pascalReadout *
        (1 -
          apparatus.referenceState.gasColumnHeight.metreReadout *
              apparatus.measuredState.temperature.kelvinReadout /
            (apparatus.measuredState.gasColumnHeight.metreReadout *
              apparatus.referenceState.temperature.kelvinReadout)) := by
  sorry

end

end IPhO2026Problems.IPhO2026_4_B_4
... [leading content omitted]
```

### Blueprint excerpt
```tex
Assuming dry air plus water vapor and zero vapor pressure at T\_0, express P\_v using P\_atm, H\_0, H, T\_0, and T.

\paragraph{Current subquestion.}
Assuming dry air plus water vapor and zero vapor pressure at T\_0, express P\_v using P\_atm, H\_0, H, T\_0, and T.

\paragraph{Recorded answer/context.}
P\_v = P\_atm*[1 - (H\_0*T)/(H*T\_0)].

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-12.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.3. Question: Extrapolate the B2 graph to determine H\_0 at 0 degrees Celsius. Reusable conclusions: Official sample: H\_0 = 5.9 cm, corresponding to V\_0 = 53.4 mL. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_B\_4.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_B_4:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_4_B_4.lean.md`
```markdown
g-law interface sufficient to
  derive the answer while exposing every substantive equation.
- `ClausiusClapeyronContext` and `ObeysClausiusClapeyron` preserve the quoted
  surrounding law and later-fit quantities without incorrectly making that law
  a premise of the B.4 calibration derivation.

## Grounding gaps

- No ready-made Physlib/Mathlib declaration was found for Dalton partial
  pressure additivity, the Figure 19 water-level pressure balance, a uniform
  cylindrical gas-volume law, or the required two-state fixed-dry-air
  ideal-gas invariant with SI readouts. These are encoded as explicit,
  constraining local equations.
- The optional `archon dag-query` executable was not available on `PATH`.
  The blueprint itself specifies only B.3 as a natural-language prerequisite,
  which is recorded locally without a sibling Lean import.

## Verification

- `mcp__archon_lean_lsp.lean_diagnostic_messages`: no errors and exactly one
  expected `declaration uses sorry` warning.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_B_4.lean`: exit code 0
  with exactly the same expected warning.
- `archon-protected.yaml` contains no active protected declarations affecting
  this file.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_B_4.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 26. `IPhO2026Problems/problem_IPhO_2026_4_B_6.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 16.338
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_B_6.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_4_B_6.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_B_6.md`

### Lean excerpt
```lean
uncertainty_of_extensivity
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hMass : 0 < waterMolarMass.central)
    (hExtensive :
      VaporizationExtensivity batch molarLatentHeat waterMolarMass
        specificLatentHeat) :
    specificLatentHeat.uncertainty =
      molarLatentHeat.uncertainty / waterMolarMass.central := by
  sorry

/-- The rounded B.5 input `39 ± 2 kJ/mol`, divided by `0.018 kg/mol`, is
compatible with the official B.6 report `2190 ± 110 kJ/kg`.

The tolerance `2 kJ/kg` applies only to rounding the propagated uncertainty;
the central-value comparison uses the propagated uncertainty interval itself. -/
lemma official_specific_latent_heat_report
    (plot : ClausiusClapeyronPlot)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hB5 : PreviousPartB5Result plot molarLatentHeat)
    (hMolarMass : WaterMolarMassData waterMolarMass)
    (hCentral :
      specificLatentHeat.central =
        molarLatentHeat.central / waterMolarMass.central)
    (hUncertainty :
      specificLatentHeat.uncertainty =
        molarLatentHeat.uncertainty / waterMolarMass.central) :
    CompatibleReportedMeasurement specificLatentHeat 2190 110 2 := by
  sorry

/-- IPhO 2026 Problem 4 B.6: converting the B.5 molar latent heat by the
water molar mass gives the latent heat of vaporization per unit mass, propagates
its uncertainty, and supports the official `2190 ± 110 kJ/kg` report. -/
theorem latent_heat_of_vaporization_per_unit_mass
    (experiment : WaterVaporExperiment)
    (plot : ClausiusClapeyronPlot)
    (batch : VaporizationBatch)
    (molarLatentHeat : Measurement .kilojoulePerMole)
    (waterMolarMass : Measurement .kilogramPerMole)
    (specificLatentHeat : Measurement .kilojoulePerKilogram)
    (hThermodynamics : VaporPressureLaws experiment molarLatentHeat)
    (hB5 : PreviousPartB5Result plot molarLatentHeat)
    (hMolarMass : WaterMolarMassData waterMolarMass)
    (hExtensive :
      VaporizationExtensivity batch molarLatentHeat waterMolarMass
        specificLatentHeat) :
    specificLatentHeat.central =
        molarLatentHeat.central / waterMolarMass.central ∧
      specificLatentHeat.uncertainty =
        molarLatentHeat.uncertainty / waterMolarMass.central ∧
      CompatibleReportedMeasurement specificLatentHeat 2190 110 2 := by
  sorry

end IPhO2026Problems.IPhO2026_4_B_6
... [leading content omitted]
```

### Blueprint excerpt
```tex
12.

Current subquestion:
Convert Q\_v into latent heat per unit mass L\_v and state the formula.

\paragraph{Current subquestion.}
Convert Q\_v into latent heat per unit mass L\_v and state the formula.

\paragraph{Recorded answer/context.}
L\_v = Q\_v/M\_0 = 2190 +/- 110 kJ/kg.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-12.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source B.5. Question: Construct a Clausius-Clapeyron graph and use it to determine the molar latent heat Q\_v. Reusable conclusions: Plot ln(P\_v/P\_atm) against 1/T; official sample slope is -4700 +/- 200 K and Q\_v = 39 +/- 2 kJ/mol. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_B\_6.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_B_6:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_4_B_6.lean.md`
```markdown
mole/amount-of-substance dimension or measurement-uncertainty structure
  suitable for `kJ/mol`, `kg/mol`, and `kJ/kg`. The indexed local measurement
  abstraction fills this gap.
- **Source rounding gap:** the rounded B.5 sample `39 ± 2 kJ/mol` divided by
  `0.018 kg/mol` is not literally the exact pair `2190 ± 110 kJ/kg`. The
  contract preserves the exact quotient and exact propagated uncertainty, and
  represents the printed B.6 pair with an explicit, proof-relevant
  compatibility relation. A future blueprint expansion should document the
  official solution's unrounded intermediate value or rounding convention if
  available.
- **`Pᵥ₀` ambiguity:** the chapter simultaneously says vapor pressure at
  freezing is taken as zero and places `Pᵥ₀` in a logarithmic denominator.
  The file keeps a zero freezing-point approximation and a separate positive
  Clausius normalization pressure, avoiding a contradictory `log(Pᵥ/0)` model.
- **Dependency navigation:** `archon dag-query` returned no node/ancestor data
  for the generic blueprint label. The chapter explicitly requires the B.5
  conclusion to be carried as natural-language input only, so no sibling Lean
  import was introduced.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_B_6.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 27. `IPhO2026Problems/problem_IPhO_2026_4_C_6.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 17.616
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_6.tex`
- Reports: `.archon/task_results/problem_IPhO_2026_4_C_6.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_C_6.md`

### Lean excerpt
```lean
e| ≤
    siValue measurement.slopeUncertainty

/-- A resistance estimate with a symmetric absolute uncertainty in `K/W`. -/
structure ResistanceEstimate where
  nominalResistance : DimThermalResistance
  resistanceUncertainty : DimThermalResistance

/-- The official sample readout `1.17 ± 0.03 K/W`. -/
def officialSampleEstimate : ResistanceEstimate where
  nominalResistance := quantityOfSI thermalResistanceDimension 1.17
  resistanceUncertainty := quantityOfSI thermalResistanceDimension 0.03

/-! ## Current C.6 conclusions -/

/--
The effective wall resistance is obtained by solving the C.5 slope relation.
No C.6 answer is included in the hypotheses: `previousPart.slopeLaw` is exactly
the reusable C.5 conclusion recorded in the source.
-/
theorem determineEffectiveWallThermalResistance
    (e : ThermalExperiment)
    (geometryValid : e.geometry.Valid)
    (parametersValid : e.ValidParameters)
    (laws : e.SatisfiesLaws)
    (graph : C5GraphReadout e)
    (previousPart : C5PreviousPartResult e graph) :
    siValue e.effectiveWallThermalResistance =
      1 /
        (siValue e.waterSpecificHeatCapacity *
          siValue e.innerWaterMass *
          siValue graph.fittedSlope) := by
  sorry

/--
Propagation of a symmetric C.5 slope uncertainty through the reciprocal
resistance formula.  The resulting interval is asymmetric in principle; this
theorem gives a conservative symmetric bound about the nominal reciprocal.
-/
theorem determineEffectiveWallThermalResistanceWithUncertainty
    (e : ThermalExperiment)
    (geometryValid : e.geometry.Valid)
    (parametersValid : e.ValidParameters)
    (laws : e.SatisfiesLaws)
    (graph : C5GraphReadout e)
    (previousPart : C5PreviousPartResult e graph)
    (measurement : SlopeMeasurement)
    (measurementValid : measurement.ValidFor graph.fittedSlope) :
    |siValue e.effectiveWallThermalResistance -
        1 /
          (siValue e.waterSpecificHeatCapacity *
            siValue e.innerWaterMass *
            siValue measurement.nominalSlope)| ≤
      siValue measurement.slopeUncertainty /
        (siValue e.waterSpecificHeatCapacity *
          siValue e.innerWaterMass *
          siValue measurement.nominalSlope *
          (siValue measurement.nominalSlope -
            siValue measurement.slopeUncertainty)) := by
  sorry

/-- The two scalar SI components of the official sample estimate. -/
theorem officialSampleEstimateReadout :
    siValue officialSampleEstimate.nominalResistance = 1.17 ∧
    siValue officialSampleEstimate.resistanceUncertainty = 0.03 := by
  sorry

end IPhO2026_4_C_6
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
termine the effective wall thermal resistance R\_Th from the C5 graph.

\paragraph{Current subquestion.}
Determine the effective wall thermal resistance R\_Th from the C5 graph.

\paragraph{Recorded answer/context.}
R\_Th = 1/(c\_0*m*slope). Official sample: R\_Th = 1.17 +/- 0.03 K/W.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-13.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.5. Question: Graph the finite-difference rate (T\_IC,j-T\_IC,j-1)/(t\_j-t\_j-1) against the corresponding average T\_OC-T\_IC. Reusable conclusions: The graph is linear, with slope 1/(c\_0*m*R\_Th) under the stated model. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_C\_6.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_C_6:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `problem_IPhO_2026_4_C_6.lean.md`
```markdown
error inequality needed for propagation.

## Grounding gaps and redraft requests

- LeanExplore found no ready-made Physlib thermal resistance, thermal
  conductivity, temperature-gradient, heat-flow-rate, or measurement
  uncertainty API. Correct derived dimensions and explicit local relations
  were used instead.
- The authorized source-page image does not show Figure 17's numerical cylinder
  dimensions. A future plan/review pass should add those constants only if an
  authorized source image containing Figure 17 is supplied.
- The fixed official `1.17 ± 0.03 K/W` sample cannot be linked to a raw C.5
  regression without its fitted slope, slope uncertainty, mass, and `c₀`
  readouts. If such raw values are supplied, add a theorem instantiating the
  general uncertainty result; do not add the numerical C.6 answer as a premise.
- `archon dag-query` could not be run because `archon` was not on `PATH` in
  this prover environment. No sibling dependency was needed.

## Verification

- Lean LSP diagnostics: only the three expected `declaration uses sorry`
  warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_4_C_6.lean`: exit code 0,
  with the same three expected warnings.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_C_6.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 28. `IPhO2026Problems/problem_IPhO_2026_4_C_7.lean`

- Compile status: passed
- Open sorries: 3
- Direct-check seconds: 16.348
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_4_C_7.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_4_C_7.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_C_7.md`

### Lean excerpt
```lean
innerRadiusMeter e.wall < outerRadiusMeter e.wall)
    (hHeight : 0 < conductingHeightMeter e.wall)
    (hOuterHotter : e.innerTemperatureKelvin t < e.outerTemperatureKelvin t) :
    e.acrylicConductivity.val =
      Real.log (outerRadiusMeter e.wall / innerRadiusMeter e.wall) /
        (2 * Real.pi * conductingHeightMeter e.wall *
          e.thermalResistance.central.val) := by
  sorry

/--
First-order root-sum-square propagation of the independent diameter,
wall-thickness, and thermal-resistance standard uncertainties through the
cylindrical-wall conductivity formula.  No height uncertainty is included
because the source gives the 10 cm height as a setpoint without an uncertainty.
-/
def conductivityStandardUncertainty
    (g : CylindricalWallGeometry)
    (thermalResistance : ExperimentalMeasurement thermalResistanceDimension) : ℝ :=
  let d := g.innerCylinderBoreDiameter.central.val
  let uD := g.innerCylinderBoreDiameter.standardUncertainty.val
  let w := g.innerCylinderAcrylicThickness.central.val
  let uW := g.innerCylinderAcrylicThickness.standardUncertainty.val
  let h := conductingHeightMeter g
  let rTh := thermalResistance.central.val
  let uRTh := thermalResistance.standardUncertainty.val
  let sensitivityDiameter :=
    (-2 * w / (d * (d + 2 * w))) / (2 * Real.pi * h * rTh)
  let sensitivityThickness :=
    (2 / (d + 2 * w)) / (2 * Real.pi * h * rTh)
  let sensitivityResistance :=
    -Real.log ((d + 2 * w) / d) / (2 * Real.pi * h * rTh ^ 2)
  Real.sqrt
    ((sensitivityDiameter * uD) ^ 2 +
     (sensitivityThickness * uW) ^ 2 +
     (sensitivityResistance * uRTh) ^ 2)

/-- `actual` rounds to `reported` at a given reporting step. -/
def RoundsTo (step actual reported : ℝ) : Prop :=
  0 < step ∧ abs (actual - reported) ≤ step / 2

/--
The Figure 17 dimensions and the C.6 resistance readout give the official
sample report `λ = 0.25 ± 0.01 W/(m*K)`.  The first component rounds the
conductivity itself; the second rounds its propagated standard uncertainty.
-/
theorem official_sample_conductivity
    (e : CylindricalConductionExperiment)
    (hFigure : Figure17AndCProcedureReadout e.wall)
    (hPrevious : PreviousPartC6Readout e)
    (hResistance : HeatResistanceLaw e)
    (hFourier : RadialFourierLaw e)
    (t : ℝ)
    (hOuterHotter : e.innerTemperatureKelvin t < e.outerTemperatureKelvin t) :
    RoundsTo ((1 : ℝ) / 100) e.acrylicConductivity.val ((1 : ℝ) / 4) ∧
      RoundsTo ((1 : ℝ) / 100)
        (conductivityStandardUncertainty e.wall e.thermalResistance)
        ((1 : ℝ) / 100) := by
  sorry

end

end IPhO2026_4_C_7
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
relation and radial Fourier law to determine acrylic conductivity lambda.

\paragraph{Current subquestion.}
Combine the heat-flow relation and radial Fourier law to determine acrylic conductivity lambda.

\paragraph{Recorded answer/context.}
lambda = ln(r\_2/r\_1)/(2*pi*h*R\_Th). Official sample: lambda = 0.25 +/- 0.01 W/(m*K).

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/E1\_page-14.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.6. Question: Determine the effective wall thermal resistance R\_Th from the C5 graph. Reusable conclusions: R\_Th = 1/(c\_0*m*slope). Official sample: R\_Th = 1.17 +/- 0.03 K/W. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_4\_C\_7.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
\label{thm:physics:IPhO_2026_4_C_7:target}
The assigned autoformalize agent should translate this physics problem into Lean declarations in the covered file, with theorem and lemma proof bodies written as `by sorry`.
\end{theorem}
\begin{proof}
This is an autoformalization task, not a proof task. Produce statements that can later be proved by the physics prover without weakening the physical model.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_4_C_7.lean.md`
```markdown
e predicate.

## Grounding gaps and redraft requests

- **Thermal-conduction API gap:** LeanExplore found no Mathlib/Physlib
  declaration for radial Fourier heat conduction or cylindrical thermal
  resistance.  `HeatResistanceLaw` and `RadialFourierLaw` are faithful local
  interfaces filling this gap.
- **Specialized unit-type gap:** Physlib supplies the foundational dimension
  algebra and `WithDim`, but the search returned no ready-made power,
  thermal-resistance, or thermal-conductivity quantity.  These roles are
  represented as `WithDim` at explicitly constructed dimensions.
- **Height-uncertainty source gap:** no uncertainty accompanies the 10 cm
  height setpoint, so the propagation contract does not invent one.
- **Blueprint link gap:** the generic theorem environment has no declaration
  name.  A future plan/review pass should add the recommended `\lean{...}`
  links above; the prover did not edit the protected blueprint domain.
- **Dependency navigation tooling gap:** the prompt said `archon` was on
  `PATH`, but `archon dag-query ...` failed with `archon: command not found`.
  No dependency was required because C.6 is explicitly a natural-language
  prerequisite only.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_4_C_7.md`
```markdown
formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)

## Local abstractions introduced

- None detected from blueprint Lean references.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

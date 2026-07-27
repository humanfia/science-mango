# Deterministic Plan Candidate Pack

Iteration: 003
Exact objective count: 22

The loop has already selected and written these objectives. Do not scan
the rest of the corpus and do not replace, reorder, add, or remove targets.
Use the excerpts below only to write a concise per-target proof strategy.

## 1. `IPhO2026Problems/problem_IPhO_2026_1_A_1.lean`

- Open placeholders: 6
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_A_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
val *
        gate.geometry.effectiveWeightLeverArm.val
  lowerEdgeContactTorque_eq :
    gate.lowerEdgeContactTorque.val =
      gate.lowerEdgeContactForce.val * gate.geometry.lowerContactLeverArm.val

/--
The limiting configuration described in the official solution: the lower
edge of the opening has just lost contact with the cube, the hinge contributes
no torque about `O`, and the two oppositely oriented torque magnitudes balance.
-/
structure AtMaximumPermissibleDifference (gate : HydrostaticGate) : Prop where
  pressure_torque_orientation :
    gate.pressureTorqueSense = .counterclockwise
  effective_weight_torque_orientation :
    gate.effectiveWeightTorqueSense = .clockwise
  lowerEdgeContactForce_zero :
    gate.lowerEdgeContactForce.val = 0
  hingeTorque_zero :
    gate.hingeTorque.val = 0
  torqueBalance :
    gate.pressureTorque.val + gate.hingeTorque.val =
      gate.effectiveWeightTorque.val + gate.lowerEdgeContactTorque.val

/-- The numerical data printed in the problem statement. -/
structure MatchesProblemData (gate : HydrostaticGate) : Prop where
  blockDensity_eq :
    gate.blockDensity.val = 3 * gate.waterDensity.val
  maximumLevelDifference_eq :
    gate.levelDifference.val = 1.41

/--
Figure 1a's slot geometry gives the effective opening area
`a² / √2`.
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
of `0.50 m`, so `0.50 m` i
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
O_2026_1_A_1.lean
% archon:source-report reports/ipho_2026/problem_IPhO_2026_1_A_1.source.json
% archon:problem-id IPhO_2026_1
% archon:part-id A.1

\chapter{Physics problem IPhO\_2026\_1\_A\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_1_A_1}

\paragraph{Problem source.}
Two water reservoirs are separated by a vertical wall MN.  A square slot of
vertical size a*sqrt(2)/2 is sealed by a fully submerged solid cube of side a
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
  \lean{IPhO2026Problems.problem_IPhO_2026_1_A_1}
  \uses{def:physics:IPhO_2026_1_A_1:aux001, def:physics:IPhO_2026_1_A_1:aux002, def:physics:IPhO_2026_1_A_1:aux003, def:physics:IPhO_2026_1_A_1:aux004, def:physics:IPhO_2026_1_A_1:aux005, def:physics:IPhO_2026_1_A_1:aux006, def:physics:IPhO_2026_1_A_1:aux007, def:physics:IPhO_2026_1_A_1:aux008, def:physics:IPhO_2026_1_A_1:aux009, def:physics:IPhO_2026_1_A_1:aux010, def:physics:IPhO_2026_1_A_1:aux011, def:physics:IPhO_2026_1_A_1:aux012, def:physics:IPhO_2026_1_A_1:aux013, def:physics:IPhO_2026_1_A_1:aux014, def:physics:IPhO_2026_1_A_1:aux015, def:physics:IPhO_2026_1_A_1:aux016, def:physics:IPhO_2026_1_A_1:aux017, lem:physics:IPhO_2026_1_A_1:aux018, lem:physics:IPhO_2026_1_A
... [suffix omitted]
```

## 2. `IPhO2026Problems/problem_IPhO_2026_1_B_1.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
itial_separation :
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
hon:source-report reports/ipho_2026/problem_IPhO_2026_1_B_1.source.json
% archon:problem-id IPhO_2026_1
% archon:part-id B.1

\chapter{Physics problem IPhO\_2026\_1\_B\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_1_B_1}

\paragraph{Problem source.}
At one instant a positron and an electron, each of mass m and charges of equal
magnitude and opposite sign, are separated by 100*a\_0.  Their velocities are
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
  \lean{IPhO2026Problem1B1.maximum_separation_for_mu_four}
  \uses{def:physics:IPhO_2026_1_B_1:aux001, def:physics:IPhO_2026_1_B_1:aux002, def:physics:IPhO_2026_1_B_1:aux003, def:physics:IPhO_2026_1_B_1:aux004, def:physics:IPhO_2026_1_B_1:aux005, def:physics:IPhO_2026_1_B_1:aux006, def:physics:IPhO_2026_1_B_1:aux007, def:physics:IPhO_2026_1_B_1:aux008, def:physics:IPhO_2026_1_B_1:aux009, def:physics:IPhO_2026_1_B_1:aux010, def:physics:IPhO_2026_1_B_1:aux011, def:physics:IPhO_2026_1_B_1:aux012, def:physics:IPhO_2026_1_B_1:aux013}
  For μ = 4, the maximum electron--positron separation is (1600 / 9) a₀.
\end{theorem}
\begin{proof}
  Use the typed geometry, governing-law, branch, and measurement interfaces listed in the decla
... [suffix omitted]
```

## 3. `IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`

- Open placeholders: 5
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
angle_range :
    0 < S.outgoingPolarAngle ∧ S.outgoingPolarAngle < Real.pi
  outgoing_conic_angle_limit :
    Tendsto S.conicAngle atTop (nhds S.outgoingPolarAngle)
  unbound_separation_limit :
    Tendsto (separationRadius S) atTop atTop
  asymptotic_relative_velocity_limit :
    Tendsto (relativeVelocity S) atTop (nhds S.asymptoticRelativeVelocity)
  asymptotic_relative_velocity_ne_zero :
    S.asymptoticRelativeVelocity ≠ 0
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
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
}
\label{ch:IPhO2026Problems_problem_IPhO_2026_1_B_2}

\paragraph{Problem source.}
At one instant a positron and an electron, each of mass m and charges of equal
magnitude and opposite sign, are separated by 100*a\_0.  Their velocities are
antiparallel and perpendicular to their separation.  Each particle has angular
momentum of magnitude mu*hbar about the center of mass.  The system is isolated,
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
  \lean{IPhO2026_1_B_2.asymptotic_relative_velocity_angle}
  \uses{def:physics:IPhO_2026_1_B_2:aux001, def:physics:IPhO_2026_1_B_2:aux002, def:physics:IPhO_2026_1_B_2:aux003, def:physics:IPhO_2026_1_B_2:aux004, def:physics:IPhO_2026_1_B_2:aux005, def:physics:IPhO_2026_1_B_2:aux006, def:physics:IPhO_2026_1_B_2:aux007, def:physics:IPhO_2026_1_B_2:aux008, def:physics:IPhO_2026_1_B_2:aux009, def:physics:IPhO_2026_1_B_2:aux010, def:physics:IPhO_2026_1_B_2:aux011, def:physics:IPhO_2026_1_B_2:aux012, def:physics:IPhO_2026_1_B_2:aux013, def:physics:IPhO_2026_1_B_2:aux014, def:physics:IPhO_2026_1_B_2:aux015, def:physics:IPhO_2026_1_B_2:aux016, def:physics:IPhO_2026_1_B_2:aux017, def:physics:IPhO_2026_1_B_2:aux018, def:physics:IPhO
... [suffix omitted]
```

## 4. `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`

- Open placeholders: 7
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
/
def HasEnoughPhotonEnergy (parameters : Parameters)
    (theta angularFrequency : ℝ) : Prop :=
  if theta < Real.pi / 2 then
    parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta angularFrequency ≤
      photonEnergy parameters angularFrequency
  else
    parameters.energyGap +
        minimumFragmentKineticEnergy parameters theta angularFrequency <
      photonEnergy parameters angularFrequency

/--
An infimum characterization of the minimum required angular frequency.

This permits the backscattering threshold to be a limiting value even when no
event with nonzero outgoing O₂ momentum occurs exactly at that value.
-/
def IsDissociationThreshold (parameters : Parameters)
    (theta threshold : ℝ) : Prop :=
  0 ≤ threshold ∧
    (∀ angularFrequency,
      KinematicallyAllowed parameters theta angularFrequency →
        threshold ≤ angularFrequency) ∧
    ∀ epsilon, 0 < epsilon →
      ∃ angularFrequency,
        KinematicallyAllowed parameters theta angularFrequency ∧
          angularFrequency < threshold + epsilon

/-- Vector conservation and the Figure 1c angle imply the scalar energy law. -/
theorem event_scalar_energy_balance
    {parameters : Parameters} {theta angularFrequency : ℝ}
    (event : DissociationEvent parameters theta angularFrequency) :
    photonEnergy parameters angularFrequency =
      parameters.energyGap +
        radialFragmentKineticEnergy parameters theta angularFrequency
          ‖event.oxygenMoleculeMomentum‖ := by
  sorry

/--
The constrained radial kinetic energy is bounded below by the appropriate
forward/backscattering infimum.
-/
theorem radialFragmentKineticEnergy_lower_bound
    {parameters : Parameters} {theta angularFrequency r : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hAngularFrequency : 0 ≤ angularFrequency)
    (hMomentumMagnitude : 0 ≤ r) :
    minimumFragmentKineticEnergy parameters theta angularFrequency ≤
      radialFragmentKineticEnergy parameters theta angularFrequency r := by
  sorry

/--
The vector event interface is neither opaque nor underdetermined: eliminating
the two momentum vectors gives exactly the scalar minimized-energy condition.
-/
theorem kinematicallyAllowed_iff_hasEnoughPhotonEnergy
    {parameters : Parameters} {theta angularFrequency : ℝ}
    (hParameters : parameters.Valid)
    (hThetaNonnegative : 0 ≤ theta)
    (hThetaAtMostPi : theta ≤ Real.pi)
    (hAngularFrequency : 0 < angularFrequency) :
    KinematicallyAllowed parameters theta angularFrequency ↔
      HasEnoughPhotonEnergy parameters theta angularFrequency := by
  sorry

/-- Clamp the Figure 1c angle to the forward limiting value `π/2`. -/
def effectiveThresholdAngle (theta : ℝ) : ℝ :=
  if theta ≤ Real.pi / 2 then theta else Real.pi / 2

/--
The threshold expression obtained from the lower root of the energy quadratic.

The factor `2` multiplying `ΔU` under the square root is present in the
official solution an
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
is absorbed by an ozone molecule O3 at rest,
dissociating it into O2 and O.  Let U\_i and U\_f be the ground-state energies of
O3 and O2 and define Delta U = U\_f - U\_i.  The outgoing O2 momentum makes angle
theta with the incident photon.  Treat the oxygen fragments classically and
non-relativistically, take the mass of an oxygen atom to be m, and use photon
momentum p\_gamma = E\_gamma/c = hbar*omega/c.

Current subquestion:
Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m.

\paragraph{Current subquestion.}
Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m.

\paragraph{Recorded answer/context.}
For theta <= pi/2, omega\_min = 3*m*c\textasciicircum{}2*[1 - sqrt(1 - (2*Delta U/(3*m*c\textasciicircum{}2))*(1 + 2*sin(theta)\textasciicircum{}2))]/[hbar*(1 + 2*sin(theta)\textasciicircum{}2)]. For theta >= pi/2 use the same threshold evaluated at theta = pi/2.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-3.png

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_C\_1.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_1_C_1:target}
  \lean{IPhO2026Problem1C1.minimumAngularFrequency_isDissociationThreshold}
  \uses{def:physics:IPhO_2026_1_C_1:aux001, def:physics:IPhO_2026_1_C_1:aux002, def:physics:IPhO_2026_1_C_1:aux003, def:physics:IPhO_2026_1_C_1:aux004, def:physics:IPhO_2026_1_C_1:aux005, def:physics:IPhO_2026_1_C_1:aux006, def:physics:IPhO_2026_1_C_1:aux007, def:physics:IPhO_2026_1_C_1:aux008, def:physics:IPhO_2026_1_C_1:aux009, def:physics:IPhO_2026_1_C_1:aux010, def:physics:IPhO_2026_1_C_1:aux011, def:physics:IPhO_2026_1_C_1:aux012, def:physics:IPhO_2026_1_C_1:aux013, def:physics:IPhO_2026_1_C_1:aux014, def:physics:IPhO_2026_1_C_1:aux015, lem:physics:IPhO_2026_1_C_1:aux016, lem:physics:IPhO_2026_1_C_1:aux017, lem:physics:IPhO_2026_1_C_1:aux018,
... [suffix omitted]
```

## 5. `IPhO2026Problems/problem_IPhO_2026_1_C_2.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
ctiveThresholdAngle setup.outgoingOxygenMoleculeAngleRad) /
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
tivistically, take the mass of an oxygen atom to be m, and use photon
momentum p\_gamma = E\_gamma/c = hbar*omega/c.

Current subquestion:
For theta = pi/6, Delta U = 1.10 eV, and m = 16.0 amu, calculate hbar*omega\_min - Delta U in eV.

\paragraph{Current subquestion.}
For theta = pi/6, Delta U = 1.10 eV, and m = 16.0 amu, calculate hbar*omega\_min - Delta U in eV.

\paragraph{Recorded answer/context.}
hbar*omega\_min - Delta U = 2.03e-11 eV.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T1\_page-3.png

\paragraph{Reusable previous-part conclusions.}
\begin{itemize}
\item Source C.1. Question: Determine the minimum angular frequency omega\_min required for dissociation at outgoing O2 angle theta, in terms of hbar, c, theta, Delta U, and m. Reusable conclusions: For theta <= pi/2, omega\_min = 3*m*c\textasciicircum{}2*[1 - sqrt(1 - (2*Delta U/(3*m*c\textasciicircum{}2))*(1 + 2*sin(theta)\textasciicircum{}2))]/[hbar*(1 + 2*sin(theta)\textasciicircum{}2)]. For theta >= pi/2 use the same threshold evaluated at theta = pi/2. Policy: natural\_language\_prerequisite\_only; do\_not\_import\_Lean\_output
\end{itemize}

\paragraph{Formalization target.}
create a compiling Lean file with sorry bodies at `IPhO2026Problems/problem\_IPhO\_2026\_1\_C\_2.lean`. The Lean declarations must preserve the physical quantities, dimensions or dimensional roles, figure labels, governing-law hypotheses, and final relation expressed by this problem.
Use Mathlib/Physlib names found through LeanExplore where available. If a physics API is missing, introduce faithful local abstractions rather than scalar placeholder aliases.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_1_C_2:target}
  \lean{IPhO2026_1_C_2.threshold_excess_energy_rounds_to_official_value}
  \uses{def:physics:IPhO_2026_1_C_2:aux001, def:physics:IPhO_2026_1_C_2:aux002, def:physics:IPhO_2026_1_C_2:aux003, def:physics:IPhO_2026_1_C_2:aux004, def:physics:IPhO_2026_1_C_2:aux005, def:physics:IPhO_2026_1_C_2:aux006, def:physics:IPhO_2026_1_C_2:aux007, def:physics:IPhO_2026_1_C_2:aux008, def:physics:IPhO_2026_1_C_2:aux009, def:physics:IPhO_2026_1_C_2:aux010, def:physics:IPhO_2026_1_C_2:aux011, def:physics:IPhO_2026_1_C_2:aux012, def:physics:IPhO_2026_1_C_2:aux013, def:physics:IPhO_2026_1_C_2:aux014, def:physics:IPhO_2026_1_C_2:aux015, def:physics:IPhO_2026_1_C_2:aux016, def:physics:IPhO_2026_1_C_2:aux017, def:physics:IPhO_2026_1_C_2:aux018, de
... [suffix omitted]
```

## 6. `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`

- Open placeholders: 4
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
ing : LimitingRayWitness experiment N xN) : Prop where
  angle_closure :
    (2 * (N : ℝ) + 1) * limiting.firstImpactPolarAngle = Real.pi

/-- The governing-law interface needed from geometric optics.

The final field makes the dependency on the equal-angle law explicit: applying
specular reflection to a positive limiting threshold produces both the
half-circle projection and the `(2N+1)` angular closure.  Neither official
closed form is a field of this structure. -/
structure HalfCylinderReflectionLaws {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) : Prop where
  obeys_specular_reflection : ObeysSpecularReflection experiment
  limiting_ray_geometry :
    ObeysSpecularReflection experiment →
      ∀ (N : ℕ) (xN : LengthQuantity),
        0 < N →
        IsPositiveReflectionThreshold experiment N xN →
        ∃ limiting : LimitingRayWitness experiment N xN,
          HalfCircleProjectionGeometry experiment N xN limiting ∧
            RepeatedReflectionClosure experiment N xN limiting

/-- Algebraic bridge from the repeated-reflection closure to the unique
limiting angle. -/
lemma limiting_first_impact_angle {mirror : HalfCylindricalMirror}
    {experiment : MultipleReflectionExperiment mirror} {N : ℕ}
    {xN : LengthQuantity} (hN : 0 < N)
    (limiting : LimitingRayWitness experiment N xN)
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

/-- Trigonometric bridge between the two official closed forms.  The Mathlib
carrier for the complementary-angle step is `Real.sin_pi_div_two_sub`. -/
lemma official_sine_cosine_forms_agree (N : ℕ) (hN : 0 < N) :
    Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) =
      Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  sorry

/-- IPhO 2026 Problem 2 A.1: the positive threshold for at most `N`
reflections in the half-cylindrical mirror has the two equivalent official
closed forms, stated on the explicitly named SI length projection. -/
theorem positive_reflection_threshold_formula
    {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror)
    (laws : HalfCylinderReflectionLaws experiment)
    (N : ℕ) (hN : 0 < N) (xN : LengthQuantity)
    (hThreshold : IsPositiveReflectionThreshold experiment N xN) :
    siLengthValue xN =
        siLengthValue mirror.radius *
          Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) ∧
      siLengthValue xN =
        siLengthValue mirror.radius *
          Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  sorry

end IPhO2026Problem2A1
```

### Blueprint excerpt
```tex
... [prefix omitted]
hon physics formalization source begin ---
% archon:physics
% archon:covers IPhO2026Problems/problem_IPhO_2026_2_A_1.lean
% archon:source-report reports/ipho_2026/problem_IPhO_2026_2_A_1.source.json
% archon:problem-id IPhO_2026_2
% archon:part-id A.1

\chapter{Physics problem IPhO\_2026\_2\_A\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_2_A_1}

\paragraph{Problem source.}
Parallel rays strike the inside of a half-cylindrical mirror of radius R.  For
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

\paragraph{Iteration 002 redraft contract.}
Import the available Physlib dimensional framework and represent the mirror
radius, incident transverse coordinate, and threshold as length quantities.
Equations involving trigonometric functions may use one explicitly named SI
length projection; angles and direction components remain dimensionless.  The
positive-threshold predicate must still express attainment and maximality, and
the equal-angle reflection law must still produce the limiting-ray projection
and the \((2N+1)\)-angle closure.  Do not retain the current undocumented
``same fixed unit'' bare-real convention.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_2_A_1:target}
  \lean{IPhO2026Problem2A1.positive_reflection_threshold_formula}
  \uses{def:physics:IPhO_2026_2_A_1:aux00
... [suffix omitted]
```

## 7. `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`

- Open placeholders: 5
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
(model : SolarOpticsModel setup) (thetaMax : ℝ) : Prop :=
  (∃ ray,
      model.isReflectedFromMirror ray ∧
      model.strikesContainer ray ∧
      model.incidenceAngleRadians ray = thetaMax) ∧
    ∀ ray,
      model.isReflectedFromMirror ray →
      model.strikesContainer ray →
      model.incidenceAngleRadians ray ≤ thetaMax

/--
The geometric extremality law saying that a largest-angle ray which still
strikes the convex cylinder is tangent to it.  This is an explicit bridge,
not an assumption about the requested coefficients.
-/
structure MaximalRayTangencyLaw
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup) : Prop where
  tangent_of_maximum :
    ∀ thetaMax, IsMaximumIncidenceAngle model thetaMax →
      ∃ ray,
        model.isReflectedFromMirror ray ∧
        model.strikesContainer ray ∧
        model.incidenceAngleRadians ray = thetaMax ∧
        LimitingTangentRay setup
          (model.incidencePointMeters ray) (model.reflectedDirection ray)

/-- Elimination form of the maximal-ray tangency law. -/
theorem maximum_incidence_ray_is_tangent
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup)
    (law : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (hMax : IsMaximumIncidenceAngle model thetaMax) :
    ∃ ray,
      model.isReflectedFromMirror ray ∧
      model.strikesContainer ray ∧
      model.incidenceAngleRadians ray = thetaMax ∧
      LimitingTangentRay setup
        (model.incidencePointMeters ray) (model.reflectedDirection ray) := by
  sorry

/--
Tangency converts the physical container radius into the signed perpendicular
distance from the ray to the container center.
-/
theorem limiting_tangent_radius_eq_signedDistance
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
This functional reading is the coefficient-identification conten
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
reports/ipho_2026/problem_IPhO_2026_2_B_1.source.json
% archon:problem-id IPhO_2026_2
% archon:part-id B.1

\chapter{Physics problem IPhO\_2026\_2\_B\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_2_B_1}

\paragraph{Problem source.}
A half-cylindrical mirror of radius R illuminates a fully absorbing cylindrical
container of radius a.  Their axes are parallel, and the container center lies
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
  \lean{IPhO2026Problems.IPhO2026_2_B_1.coefficients_from_solar_cooker_geometry}
  \uses{def:physics:IPhO_2026_2_B_1:aux001, def:physics:IPhO_2026_2_B_1:aux002, def:physics:IPhO_2026_2_B_1:aux003, def:physics:IPhO_2026_2_B_1:aux004, def:physics:IPhO_2026_2_B_1:aux005, def:physics:IPhO_2026_2_B_1:aux006, def:physics:IPhO_2026_2_B_1:aux007, def:physics:IPhO_2026_2_B_1:aux008, def:physics:IPhO_2026_2_B_1:aux009, def:physics:IPhO_2026_2_B_1:aux010, def:physics:IPhO_2026_2_B_1:aux011, def:physics:IPhO_2026_2_B_1:aux012, def:physics:IPhO_2026_2_B_1:aux013, def:physics:IPhO_2026_2_B_1:aux014, def:physics:IPhO_2026_2_B_1:aux015, def:physics:IPhO_2026_2_B_1:aux016, def:physics:IPhO_2026_2_B_1:aux017, def:physics:IPhO_2026_2_B_1:au
... [suffix omitted]
```

## 8. `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`

- Open placeholders: 3
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
l ray ≤ s.thetaMax
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
al mirror of radius R illuminates a fully absorbing cylindrical
container of radius a.  Their axes are parallel, and the container center lies
R/2 from the mirror center on the symmetry plane.  Uniform parallel sunlight
arrives along the optical axis.  Any ray absorbed by the container reflects at
most once.  Let theta\_max be the largest incidence angle on the mirror among
rays that strike the container, and let P\_0 be the power the cylinder would
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
  \lean{IPhO2026Problems.IPhO_2026_2_B_2.power_ratio_eq_one_div_one_sub_cos}
  \uses{def:physics:IPhO_2026_2_B_2:aux001, def:physics:IPhO_2026_2_B_2:aux002, def:physics:IPhO_2026_2_B_2:aux003, def:physics:IPhO_2026_2_B_2:aux004, def:physics:IPhO_2026_2_B_2:aux005, def:physics:IPhO_2026_2_B_2:aux006, def:physics:IPhO_2026_2_B_2:aux007, def:physics:IPhO_2026_2_B_2:aux008, def:physics:IPhO_2026_2_B_2:aux009, def:physics:IPhO_2026_2_B_2:aux010, lem:physics:IPhO_2026_2_B_2:aux011, lem:physics:IPhO_2026_2_B_2:aux012}
  For the Figure 2f solar cooker, the actual-to-no-mirror received-power ratio is 1 / (1 - cos θ\_max).
\end{theorem}
\begin{proof}
  Use the typed geometry, governing-law, branch, and measurement interfaces listed
... [suffix omitted]
```

## 9. `IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`

- Open placeholders: 3
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_3.tex`

### Lean excerpt
```lean
... [prefix omitted]
1
  absorbed_ray_reflects_at_most_once :
    cooker.maxReflectionsForAbsorbedRay ≤ 1
  thetaMax_nonnegative : 0 ≤ cooker.thetaMax
  thetaMax_le_pi_div_two : cooker.thetaMax ≤ Real.pi / 2

/--
The reusable conclusions of parts B.1 and B.2, restated locally because this
lane must not import sibling problem files.

The first equation is the Figure 2f cutoff-ray geometry.  The second is the
received-power law for uniform parallel illumination and a fully absorbing
container in the one-reflection regime.
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
      lengthInCentime
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
is.  Any ray absorbed by the container reflects at
most once.  Let theta\_max be the largest incidence angle on the mirror among
rays that strike the container, and let P\_0 be the power the cylinder would
receive without the mirror.  See Figure 2f.

Current subquestion:
For R = 1.0 m, find a such that P = 5*P\_0, and report it in cm.

\paragraph{Current subquestion.}
For R = 1.0 m, find a such that P = 5*P\_0, and report it in cm.

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
  \lean{IPhO2026Problem2B3.ipho2026_problem2_B3}
  \uses{def:physics:IPhO_2026_2_B_3:aux001, def:physics:IPhO_2026_2_B_3:aux002, def:physics:IPhO_2026_2_B_3:aux003, def:physics:IPhO_2026_2_B_3:aux004, def:physics:IPhO_2026_2_B_3:aux005, def:physics:IPhO_2026_2_B_3:aux006, def:physics:IPhO_2026_2_B_3:aux007, def:physics:IPhO_2026_2_B_3:aux008, def:physics:IPhO_2026_2_B_3:aux009, def:physics:IPhO_2026_2_B_3:aux010, def:physics:IPhO_2026_2_B_3:aux011, def:physics:IPhO_2026_2_B_3:aux012, lem:physics:IPhO_2026_2_B_3:aux013, lem:physics:IPhO_2026_2_B_3:aux014}
  Answer to IPhO 2026 theoretical problem 2, part B.3: the operating point has cos θ\_max = 4/5, and the required radius is 0.12 m = 12 cm.
\end{theorem}
\begin{proof}
... [suffix omitted]
```

## 10. `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`

- Open placeholders: 4
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
retained for the later caustic construction: ray B is parallel to
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
    lengthInMetres interaction.bA =
      lengthInMetres mirror.radius / (2 * Real.cos incidenceAngle) := by
  sorry

/-- **IPhO 2026, Problem 2, C.1.**  In the Figure 2g coordinate convention,
the reflected ray A has slope `cot (2 * theta)` and intercept
`R / (2 * cos theta)`. -/
theorem rayA_slope_and_intercept
    (mirror : HalfCylindricalMirror) (theta : ℝ)
    (setup : Figure2gCausticSetup mirror theta) :
    setup.rayA.mA = Real.cot (2 * theta) ∧
      lengthInMetres setup.rayA.bA =
        lengthInMetres mirror.radius / (2 * Real.cos theta) := by
  sorry

end

end IPhO2026_2_C_1
end IPhO2026Problems
```

### Blueprint excerpt
```tex
... [prefix omitted]
ormalization source begin ---
% archon:physics
% archon:covers IPhO2026Problems/problem_IPhO_2026_2_C_1.lean
% archon:source-report reports/ipho_2026/problem_IPhO_2026_2_C_1.source.json
% archon:problem-id IPhO_2026_2
% archon:part-id C.1

\chapter{Physics problem IPhO\_2026\_2\_C\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_2_C_1}

\paragraph{Problem source.}
For the half-cylindrical mirror of radius R, ray A is incident at angle theta
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

\paragraph{Iteration 002 redraft contract.}
Import Physlib and make the mirror radius, point coordinates, and line
intercept length-valued.  If the analytic geometry is written in scalar
coordinates, expose a named SI-length projection and state every coordinate
and intercept equation through it.  The slope, angles, and normalized
direction components are dimensionless.  Preserve the upward incoming ray,
radial outward normal, down-left reflected branch, and the vector
specular-reflection equation.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_2_C_1:target}
  \lean{IPhO2026Problems.IPhO2026_2_C_1.rayA_slope_and_intercept}
  \uses{def:physics:IPhO_2026_2_C_1:aux001, def:physics:IPhO_2026_2_C_1:aux002, def:physics:IPhO_2026_2_C_1:aux003, def:physics:IPhO_2026_2_C_1:aux004, def:phys
... [suffix omitted]
```

## 11. `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
os ray.incidenceAngle) :=
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
        lengthSI (rayB Δθ).reflectedLine.yIntercept -
          (lengthSI mirror.radius / (2 * Real.cos θ) *
            (1 + Real.tan θ * Δθ)))
        =O[𝓝 (0 : ℝ)] (fun Δθ : ℝ => Δθ ^ 2)) := by
  sorry

end IPhO2026Problems.IPhO2026_2_C_2
```

### Blueprint excerpt
```tex
... [prefix omitted]
mirror of radius R, ray A is incident at angle theta
and its reflected line is y = m\_A*x + b\_A.  A neighboring parallel ray B is
incident at theta + Delta theta, with Delta theta much smaller than theta, and
its reflected line is y = m\_B*x + b\_B.  The envelope/intersection of neighboring
rays forms the caustic.  Use Figure 2g and its coordinate convention.

Current subquestion:
Expand m\_B and b\_B to first order in Delta theta.

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

\paragraph{Iteration 002 redraft contract.}
Use the same Physlib-backed length carrier and named SI projection as C.1 for
the mirror radius, coordinates, and intercept.  The slope and angular
increment are dimensionless.  Keep the conclusion as two genuine local
first-order expansions with quadratic remainders; for the intercept, apply
the asymptotic statement to its SI-length projection rather than replacing a
length by a bare real.  Retain the nonzero sine/cosine conditions and the
Figure 2g incoming/outgoing orientation.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_2_C_2:target}
  \lean{IPhO2026Problems.IPhO2026_2_C_2.rayB_firstOrderExpansion}
  \uses{def:physics:IPhO_2026_2_C_2:aux001, def:physics:IPhO_2026_2_C_2:aux002, def:physics:IPhO_2026_2_C_2:aux003, def:physics:IPhO_2
... [suffix omitted]
```

## 12. `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`

- Open placeholders: 6
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_3.tex`

### Lean excerpt
```lean
... [prefix omitted]
ate unit. -/
def reflectedIntercept (R α : ℝ) : ℝ :=
  R / (2 * Real.cos α)

/-- The affine support line of the reflected ray at incidence angle `α`. -/
def LiesOnReflectedSupport (R α : ℝ) (p : PlanarPoint) : Prop :=
  yCoord p = reflectedSlope α * xCoord p + reflectedIntercept R α

/-- Governing geometry and reflection data for Figure 2g.

All incoming rays share the displayed vertical direction, so rays indexed by
`θ` and `θ + Δθ` are parallel before reflection.  The last field is the
reusable C.1 reflection law; it constrains every point of the outgoing branch
by an explicit affine equation and does not prescribe the caustic. -/
structure Figure2gOptics (R : ℝ) where
  radiusPositive : 0 < R
  incomingDirectionX : ℝ
  incomingDirectionY : ℝ
  incomingVertical : incomingDirectionX = 0
  incomingForward : 0 < incomingDirectionY
  incomingImpact : ℝ → PlanarPoint
  incomingImpact_eq :
    ∀ α, IsAdmissibleAngle α → incomingImpact α = impactPoint R α
  reflectedRay : ℝ → OrientedRay2D
  reflectedStartsAtImpact :
    ∀ α, IsAdmissibleAngle α →
      (reflectedRay α).vertex = incomingImpact α
  reflectedLineLaw :
    ∀ α, IsAdmissibleAngle α → ∀ p,
      (reflectedRay α).Contains p → LiesOnReflectedSupport R α p

/-- The incidence point given by the Figure 2g coordinate readout lies on the
upper semicircular mirror. -/
theorem impactPoint_on_upperSemicircularMirror
    (R α : ℝ) (hR : 0 < R) (hα : IsAdmissibleAngle α) :
    OnUpperSemicircularMirror R (impactPoint R α) := by
  sorry

/-- The explicit, constraining meaning of being the intersection of reflected
ray `A` at `θ` and neighboring reflected ray `B` at `θ + δ`. -/
def IsNeighboringReflectedIntersection {R : ℝ}
    (model : Figure2gOptics R) (θ δ : ℝ) (p : PlanarPoint) : Prop :=
  0 < δ ∧
  IsAdmissibleAngle θ ∧
  IsAdmissibleAngle (θ + δ) ∧
  (model.reflectedRay θ).Contains p ∧
  (model.reflectedRay (θ + δ)).Contains p

/-- Remainder in the C.2 first-order expansion of the neighboring reflected
ray's slope.  The coefficient `2 / sin(2θ)^2` is `2 csc(2θ)^2`. -/
def slopeFirstOrderRemainder (θ δ : ℝ) : ℝ :=
  reflectedSlope (θ + δ) -
    (reflectedSlope θ - 2 / Real.sin (2 * θ) ^ 2 * δ)

/-- Remainder in the C.2 first-order expansion of the neighboring reflected
ray's intercept. -/
def interceptFirstOrderRemainder (R θ δ : ℝ) : ℝ :=
  reflectedIntercept R (θ + δ) -
    (reflectedIntercept R θ * (1 + Real.tan θ * δ))

/-- The precise `O(Δθ²)` interpretation of both first-order expansions quoted
from part C.2. -/
def HasFigure2gFirstOrderExpansions (R θ : ℝ) : Prop :=
  IsBigO (𝓝 (0 : ℝ)) (slopeFirstOrderRemainder θ) (fun δ : ℝ => δ ^ 2) ∧
  IsBigO (𝓝 (0 : ℝ)) (interceptFirstOrderRemainder R θ) (fun δ : ℝ => δ ^ 2)

/-- The reusable result of part C.2, formulated with an actual asymptotic error
rather than an informal truncation symbol. -/
theorem previousPartC2_firstOrderExpansions
    (R θ : ℝ) (hθ : IsAdmissibleAngle θ) :
    HasFigure2gFirstOrderExpansions R θ := by
  sorry

/-- The inters
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
coordinate convention.

Current subquestion:
Find the limiting intersection coordinates (X\_c,Y\_c) of the neighboring reflected rays.

\paragraph{Current subquestion.}
Find the limiting intersection coordinates (X\_c,Y\_c) of the neighboring reflected rays.

\paragraph{Recorded answer/context.}
X\_c = R*sin(theta)\textasciicircum{}3; Y\_c = (R/2)*cos(theta)*(2 - cos(2*theta)).

\paragraph{Figure/image path.}
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
  \lean{IPhO2026Problems.IPhO2026_2_C_3.limitingIntersectionCoordinates}
  \uses{def:physics:IPhO_2026_2_C_3:aux001, def:physics:IPhO_2026_2_C_3:aux002, def:physics:IPhO_2026_2_C_3:aux003, def:physics:IPhO_2026_2_C_3:aux004, lem:physics:IPhO_2026_2_C_3:aux005, lem:physics:IPhO_2026_2_C_3:aux006, def:physics:IPhO_2026_2_C_3:aux007, def:physics:IPhO_2026_2_C_3:aux008, def:physics:IPhO_2026_2_C_3:aux009, def:physics:IPhO_2026_2_C_3:aux010, def:physics:IPhO_2026_2_C_3:aux011, def:physics:IPhO_2026_2_C_3:aux012, def:physics:IPhO_2026_2_C_3:aux013, def:physics:IPhO_2026_2_C_3:aux014, def:physics:IPhO_2026_2_C_3:aux015, lem:physics:IPhO_2026_2_C_3:aux016, def:physics:IPhO_2026_2_C_3:aux017, def:physics:IPhO_2026_2_C_3:aux018, de
... [suffix omitted]
```

## 13. `IPhO2026Problems/problem_IPhO_2026_2_C_4.lean`

- Open placeholders: 2
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_4.tex`

### Lean excerpt
```lean
... [prefix omitted]
tedRayReadout :=
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
_A*x + b\_A.  A neighboring parallel ray B is
incident at theta + Delta theta, with Delta theta much smaller than theta, and
its reflected line is y = m\_B*x + b\_B.  The envelope/intersection of neighboring
rays forms the caustic.  Use Figure 2g and its coordinate convention.

Current subquestion:
For theta << 1, put the caustic in the form Y\_c = v*|X\_c|\textasciicircum{}(p/q) + u. Determine u, v, and the integers p,q.

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
  \lean{IPhO2026Problems.IPhO2026_2_C_4.smallAngleCausticPowerLaw}
  \uses{def:physics:IPhO_2026_2_C_4:aux001, def:physics:IPhO_2026_2_C_4:aux002, def:physics:IPhO_2026_2_C_4:aux003, def:physics:IPhO_2026_2_C_4:aux004, def:physics:IPhO_2026_2_C_4:aux005, def:physics:IPhO_2026_2_C_4:aux006, def:physics:IPhO_2026_2_C_4:aux007, def:physics:IPhO_2026_2_C_4:aux008, def:physics:IPhO_2026_2_C_4:aux009, def:physics:IPhO_2026_2_C_4:aux010, def:physics:IPhO_2026_2_C_4:aux011, def:physics:IPhO_2026_2_C_4:aux012, def:physics:IPhO_2026_2_C_4:aux013, lem:physics:IPhO_2026_2_C_4:aux014}
  IPhO 2026 problem 2, part C.4. The C.3 caustic has offset u = R/2, coefficient v = (3/4) R\textasciicircum{}(1/3), and reduced exponent p/q = 2/3.
\en
... [suffix omitted]
```

## 14. `IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
overning law, not as a definition of any field.
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
rchon physics formalization source begin ---
% archon:physics
% archon:covers IPhO2026Problems/problem_IPhO_2026_3_A_1.lean
% archon:source-report reports/ipho_2026/problem_IPhO_2026_3_A_1.source.json
% archon:problem-id IPhO_2026_3
% archon:part-id A.1

\chapter{Physics problem IPhO\_2026\_3\_A\_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_3_A_1}

\paragraph{Problem source.}
A homogeneous isotropic paramagnetic torus has mean radius R, inner radius r
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
  \lean{IPhO2026Problems.IPhO2026_3_A_1.fieldStrength_eq_turns_current_area_div_volume}
  \uses{def:physics:IPhO_2026_3_A_1:aux001, def:physics:IPhO_2026_3_A_1:aux002, def:physics:IPhO_2026_3_A_1:aux003, def:physics:IPhO_2026_3_A_1:aux004, def:physics:IPhO_2026_3_A_1:aux005, def:physics:IPhO_2026_3_A_1:aux006, def:physics:IPhO_2026_3_A_1:aux007, def:physics:IPhO_2026_3_A_1:aux008, def:physics:IPhO_2026_3_A_1:aux009, def:physics:IPhO_2026_3_A_1:aux010, def:physics:IPhO_2026_3_A_1:aux011, def:physics:IPhO_2026_3_A_1:aux012, def:physics:IPhO_2026_3_A_1:aux013, def:physics:IPhO_2026_3_A_1:aux014, def:physics:IPhO_2026_3_A_1:aux015, def:physics:IPhO_2026_3_A_1:aux016, def:physics:IPhO_2026_3_A_1:aux017, def:physics:IPhO_2026_3
... [suffix omitted]
```

## 15. `IPhO2026Problems/problem_IPhO_2026_3_A_2.lean`

- Open placeholders: 2
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
luxDensityChange : WithDim magneticFluxDensityDimension ℝ
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
oblems_problem_IPhO_2026_3_A_2}

\paragraph{Problem source.}
A homogeneous isotropic paramagnetic torus has mean radius R, inner radius r
with r << R, volume V, and cross-sectional area A.  An insulated conducting
wire is wound densely around it with N turns and instantaneous current I.
Fields H and B and magnetization M are approximately uniform in the torus.
Use B = mu\_0*H + mu\_0*M, Ampere's law, and the sign convention that work and
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
  \lean{IPhO2026Problems.Problem3A2.external_source_work_for_flux_density_change}
  \uses{def:physics:IPhO_2026_3_A_2:aux001, def:physics:IPhO_2026_3_A_2:aux002, def:physics:IPhO_2026_3_A_2:aux003, def:physics:IPhO_2026_3_A_2:aux004, def:physics:IPhO_2026_3_A_2:aux005, def:physics:IPhO_2026_3_A_2:aux006, def:physics:IPhO_2026_3_A_2:aux007, def:physics:IPhO_2026_3_A_2:aux008, def:physics:IPhO_2026_3_A_2:aux009, def:physics:IPhO_2026_3_A_2:aux010, def:physics:IPhO_2026_3_A_2:aux011, def:physics:IPhO_2026_3_A_2:aux012, def:physics:IPhO_2026_3_A_2:aux013, def:physics:IPhO_2026_3_A_2:aux014, def:physics:IPhO_2026_3_A_2:aux015, def:physics:IPhO_2026_3_A_2:aux016, lem:physics:IPhO_2026_3_A_2:aux017}
  IPhO 2026 Problem 3 A.2. Fo
... [suffix omitted]
```

## 16. `IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`

- Open placeholders: 4
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_3.tex`

### Lean excerpt
```lean
... [prefix omitted]
³`. -/
abbrev Volume := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Cross-sectional area, with dimension `L²`. -/
abbrev Area := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- Electric current, with dimension charge/time. -/
abbrev ElectricCurrent := Dimensionful (WithDim (C𝓭 * T𝓭⁻¹) ℝ)

/-- Magnetic field strength `H`, with SI unit A/m. -/
abbrev MagneticFieldStrength :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- Magnetization `M`, which has the same dimension as `H`. -/
abbrev Magnetization :=
  Dimensionful (WithDim (C𝓭 * T𝓭⁻¹ * L𝓭⁻¹) ℝ)

/-- Magnetic flux density `B`, with SI unit tesla. -/
abbrev MagneticFluxDensity :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Vacuum permeability `μ₀`, with SI dimension mass·length/charge². -/
abbrev VacuumPermeability :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Work/energy, grounded by Physlib's dimensionful energy type. -/
abbrev Energy := DimEnergy

/-- The numerical value of a dimensionful real quantity in SI units. -/
noncomputable def siValue {d : Dimension} (q : Dimensionful (WithDim d ℝ)) : ℝ :=
  (q.1 UnitChoices.SI).val

/-- Construct a dimensionful energy from a numerical value in joules. -/
noncomputable def energyFromSI (x : ℝ) : Energy :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨x⟩

/-- Evaluation in SI is injective on quantities of any fixed dimension. -/
theorem dimensionful_ext_si {d : Dimension}
    {x y : Dimensionful (WithDim d ℝ)}
    (h : siValue x = siValue y) :
    x = y := by
  sorry

/-- `energyFromSI` has the prescribed numerical value in joules. -/
theorem siValue_energyFromSI (x : ℝ) :
    siValue (energyFromSI x) = x := by
  sorry

/-! ## Figure and sign data -/

/-- Choice of the common positive direction around the torus. -/
inductive ToroidalOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq

/-- Sign convention for signed work increments. -/
inductive WorkSignConvention where
  | positiveIntoSystem
  | positiveOutOfSystem
  deriving DecidableEq

/--
The homogeneous isotropic paramagnetic torus and winding in Figure 3a.
The field entries are uniform components along `toroidalOrientation`.
-/
structure TorusData where
  /-- Mean radius labelled `R` in Figure 3a. -/
  meanRadiusR : Length
  /-- Minor/cross-sectional radius labelled `r` in Figure 3a. -/
  minorRadiusr : Length
  /-- Torus volume labelled `V`. -/
  volumeV : Volume
  /-- Cross-sectional area labelled `A`. -/
  crossSectionAreaA : Area
  /-- Total number of dense winding turns, labelled `N`. -/
  turnCountN : ℕ
  /-- Instantaneous current in the insulated wire, labelled `I`. -/
  currentI : ElectricCurrent
  /-- Vacuum permeability `μ₀`. -/
  vacuumPermeabilityMu0 : VacuumPermeability
  /-- Approximately uniform magnetic field-strength magnitude `H`. -/
  fieldStrengthH : MagneticFieldStrength
  /-- Approximately uniform magnetic flux-density magnitude `B`. -/
  fluxDensityB : MagneticFluxDensity
  /-- Approximately uniform magnetization magnitude `M`, pa
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
graph{Problem source.}
A homogeneous isotropic paramagnetic torus has mean radius R, inner radius r
with r << R, volume V, and cross-sectional area A.  An insulated conducting
wire is wound densely around it with N turns and instantaneous current I.
Fields H and B and magnetization M are approximately uniform in the torus.
Use B = mu\_0*H + mu\_0*M, Ampere's law, and the sign convention that work and
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
  \lean{IPhO2026Problems.Problem3A3.materialWork_eq_mu0_volume_H_dM}
  \uses{def:physics:IPhO_2026_3_A_3:aux001, def:physics:IPhO_2026_3_A_3:aux002, def:physics:IPhO_2026_3_A_3:aux003, def:physics:IPhO_2026_3_A_3:aux004, def:physics:IPhO_2026_3_A_3:aux005, def:physics:IPhO_2026_3_A_3:aux006, def:physics:IPhO_2026_3_A_3:aux007, def:physics:IPhO_2026_3_A_3:aux008, def:physics:IPhO_2026_3_A_3:aux009, def:physics:IPhO_2026_3_A_3:aux010, def:physics:IPhO_2026_3_A_3:aux011, lem:physics:IPhO_2026_3_A_3:aux012, lem:physics:IPhO_2026_3_A_3:aux013, def:physics:IPhO_2026_3_A_3:aux014, def:physics:IPhO_2026_3_A_3:aux015, def:physics:IPhO_2026_3_A_3:aux016, def:physics:IPhO_2026_3_A_3:aux017, def:physics:IPhO_2026_3_A_3:aux018, def:ph
... [suffix omitted]
```

## 17. `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`

- Open placeholders: 4
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
uationOfState :
    ∀ s,
      (process.temperature s : ℝ) *
          process.magnetizationAmperePerMetre s *
          torus.volumeCubicMetres =
        torus.amountMoles * torus.materialK_SI *
          process.fieldStrengthAmperePerMetre s
  heatCapacityLaw :
    ∀ s,
      process.heatCapacityAtConstantMagnetization s =
        torus.amountMoles * torus.materialLambda_SI /
          (process.temperature s : ℝ) ^ 2
  internalEnergyDifferentialLaw :
    ∀ s,
      process.internalEnergyRateJoules s =
        process.heatCapacityAtConstantMagnetization s *
          process.temperatureRateKelvin s
  magneticWorkLaw :
    ∀ s,
      process.workRateJoules s =
        vacuumPermeability_SI * torus.volumeCubicMetres *
          process.fieldStrengthAmperePerMetre s *
          process.magnetizationRateAmperePerMetre s
  firstLawSignConvention :
    ∀ s,
      process.internalEnergyRateJoules s =
        process.heatRateJoules s + process.workRateJoules s

/-- Along an isothermal sweep, `dU = C_M dT` forces the internal-energy
rate to vanish. -/
theorem internalEnergyRate_eq_zero
    (torus : ParamagneticTorus)
    (vacuumPermeability_SI : ℝ)
    (fixedTemperature : Temperature)
    (initialFieldStrength finalFieldStrength : ℝ)
    (process : IsothermalFieldSweep)
    (laws : SatisfiesIsothermalParamagneticTorusLaws torus
      vacuumPermeability_SI fixedTemperature initialFieldStrength
      finalFieldStrength process) :
    ∀ s, process.internalEnergyRateJoules s = 0 := by
  sorry

/-- The equation of state and the oriented linear field sweep determine the
magnetization rate. -/
theorem magnetizationRate_eq
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
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
_1}
\label{ch:IPhO2026Problems_problem_IPhO_2026_3_B_1}

\paragraph{Problem source.}
Continue with the paramagnetic torus.  Its equation of state is T*M*V = n*K*H,
its heat capacity at constant M is C\_M = n*lambda/T\textasciicircum{}2, and dU = C\_M*dT.
The volume is fixed and the magnetic work on the material is
dW = mu\_0*V*H*dM.  Work and heat entering the torus are positive.

Current subquestion:
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
  \lean{IPhO2026Problems.ProblemIPhO2026_3_B_1.heat_transferred_into_torus}
  \uses{def:physics:IPhO_2026_3_B_1:aux001, def:physics:IPhO_2026_3_B_1:aux002, def:physics:IPhO_2026_3_B_1:aux003, def:physics:IPhO_2026_3_B_1:aux004, def:physics:IPhO_2026_3_B_1:aux005, lem:physics:IPhO_2026_3_B_1:aux006, lem:physics:IPhO_2026_3_B_1:aux007, lem:physics:IPhO_2026_3_B_1:aux008}
  The heat transferred into the paramagnetic torus when the magnitude of H changes isothermally from H\_i to H\_f. The sweep parametrization records the orientation, so the same signed formula also covers a decreasing field magnitude.
\end{theorem}
\begin{proof}
  Use the typed geometry, governing-law, branch, and measurement interfaces listed in the declar
... [suffix omitted]
```

## 18. `IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`

- Open placeholders: 3
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
I s).val + (path.workInputRateSI s).val
  magnetic_work :
    ∀ s ∈ processDomain,
      (path.workInputRateSI s).val =
        model.vacuumPermeabilitySI.val * model.volumeSI.val
          * (path.fieldStrengthMagnitudeSI s).val
          * derivWithin (fun u => (path.magnetizationMagnitudeSI u).val)
              processDomain s

/-! ## Derivability bridges -/

/--
The differential laws reduce to the separable magnetocaloric ODE.  This is the
algebra-and-product-rule bridge from the physical assumptions to the invariant
used in the endpoint calculation.
-/
theorem reduced_adiabatic_temperature_ode
    (model : ParamagneticTorusModel)
    (path : AdiabaticPathReadout)
    (initialTemperature finalTemperature : TemperatureQuantity)
    (initialFieldStrength finalFieldStrength : MagneticFieldStrengthQuantity)
    (hphysics : IsAdiabaticQuasistaticChange model path
      initialTemperature finalTemperature initialFieldStrength finalFieldStrength)
    (s : ℝ) (hs : s ∈ processDomain) :
    (model.heatCapacityParameterSI.val
          + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
            * (path.fieldStrengthMagnitudeSI s).val ^ 2)
        * derivWithin (fun u => (path.temperatureSI u).val) processDomain s =
      model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * (path.fieldStrengthMagnitudeSI s).val
        * (path.temperatureSI s).val
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

The positivity assumptions in the
... [suffix omitted]
```

### Blueprint excerpt
```tex
... [prefix omitted]
26Problems_problem_IPhO_2026_3_B_2}

\paragraph{Problem source.}
Continue with the paramagnetic torus.  Its equation of state is T*M*V = n*K*H,
its heat capacity at constant M is C\_M = n*lambda/T\textasciicircum{}2, and dU = C\_M*dT.
The volume is fixed and the magnetic work on the material is
dW = mu\_0*V*H*dM.  Work and heat entering the torus are positive.

Current subquestion:
For an adiabatic change H\_i -> H\_f starting at T\_i, determine Delta T = T\_f - T\_i.

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
  \lean{IPhO2026Problems.IPhO2026_3_B_2.adiabatic_temperature_change}
  \uses{def:physics:IPhO_2026_3_B_2:aux001, def:physics:IPhO_2026_3_B_2:aux002, def:physics:IPhO_2026_3_B_2:aux003, def:physics:IPhO_2026_3_B_2:aux004, def:physics:IPhO_2026_3_B_2:aux005, def:physics:IPhO_2026_3_B_2:aux006, def:physics:IPhO_2026_3_B_2:aux007, def:physics:IPhO_2026_3_B_2:aux008, def:physics:IPhO_2026_3_B_2:aux009, def:physics:IPhO_2026_3_B_2:aux010, def:physics:IPhO_2026_3_B_2:aux011, def:physics:IPhO_2026_3_B_2:aux012, def:physics:IPhO_2026_3_B_2:aux013, def:physics:IPhO_2026_3_B_2:aux014, def:physics:IPhO_2026_3_B_2:aux015, def:physics:IPhO_2026_3_B_2:aux016, def:physics:IPhO_2026_3_B_2:aux017, def:physics:IPhO_2026_3_B_2:aux018, def:p
... [suffix omitted]
```

## 19. `IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`

- Open placeholders: 2
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_2.tex`

### Lean excerpt
```lean
... [prefix omitted]
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
relation from part B may be reused.

Current subquestion:
Express M\_1 in terms of M\_2, M\_3, and M\_4.

\paragraph{Current subquestion.}
Express M\_1 in terms of M\_2, M\_3, and M\_4.

\paragraph{Recorded answer/context.}
M\_1 = sqrt(M\_2\textasciicircum{}2 - M\_3\textasciicircum{}2 + M\_4\textasciicircum{}2), taking the nonnegative magnitude.

\paragraph{Figure/image path.}
/root/proposal\_for\_physic/science-mango/ipho\_2026\_source/image/T3\_page-3.png

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
  \lean{IPhO2026Problem3C2.magnetization_at_state_one}
  \uses{def:physics:IPhO_2026_3_C_2:aux001, def:physics:IPhO_2026_3_C_2:aux002, def:physics:IPhO_2026_3_C_2:aux003, def:physics:IPhO_2026_3_C_2:aux004, def:physics:IPhO_2026_3_C_2:aux005, def:physics:IPhO_2026_3_C_2:aux006, def:physics:IPhO_2026_3_C_2:aux007, def:physics:IPhO_2026_3_C_2:aux008, def:physics:IPhO_2026_3_C_2:aux009, def:physics:IPhO_2026_3_C_2:aux010, def:physics:IPhO_2026_3_C_2:aux011, def:physics:IPhO_2026_3_C_2:aux012, def:physics:IPhO_2026_3_C_2:aux013, def:physics:IPhO_2026_3_C_2:aux014, def:physics:IPhO_2026_3_C_2:aux015, def:physics:IPhO_2026_3_C_2:aux016, def:physics:IPhO_2026_3_C_2:aux017, def:physics:IPhO_2026_3_C_2:aux018, def:physics:IPhO_202
... [suffix omitted]
```

## 20. `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_3.tex`

### Lean excerpt
```lean
... [prefix omitted]
omCold.siValue =
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
y be reused.

Current subquestion:
Using the supplied potassium-chromate and liquid-helium data, find the helium temperature after one cycle.

\paragraph{Current subquestion.}
Using the supplied potassium-chromate and liquid-helium data, find the helium temperature after one cycle.

\paragraph{Recorded answer/context.}
Q\_c = 1.29e-1 J, so |Delta T| = 9.92e-3 K and T\_final = 0.99008 K.

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
  \lean{IPhO2026Problems.Problem3C3.IPhO_2026_3_C_3_helium_temperature_after_one_cycle}
  \uses{def:physics:IPhO_2026_3_C_3:aux001, def:physics:IPhO_2026_3_C_3:aux002, def:physics:IPhO_2026_3_C_3:aux003, def:physics:IPhO_2026_3_C_3:aux004, def:physics:IPhO_2026_3_C_3:aux005, def:physics:IPhO_2026_3_C_3:aux006, def:physics:IPhO_2026_3_C_3:aux007, def:physics:IPhO_2026_3_C_3:aux008, def:physics:IPhO_2026_3_C_3:aux009, def:physics:IPhO_2026_3_C_3:aux010, def:physics:IPhO_2026_3_C_3:aux011, def:physics:IPhO_2026_3_C_3:aux012, def:physics:IPhO_2026_3_C_3:aux013, def:physics:IPhO_2026_3_C_3:aux014, def:physics:IPhO_2026_3_C_3:aux015, def:physics:IPhO_2026_3_C_3:aux016, def:physics:IPhO_2026_3_C_3:aux017, def:physics:IPhO_2026_3
... [suffix omitted]
```

## 21. `IPhO2026Problems/problem_IPhO_2026_3_C_4.lean`

- Open placeholders: 2
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_4.tex`

### Lean excerpt
```lean
... [prefix omitted]
et.Icc 0 experiment.elapsedTime.val,
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
rchon:problem-id IPhO_2026_3
% archon:part-id C.4

\chapter{Physics problem IPhO\_2026\_3\_C\_4}
\label{ch:IPhO2026Problems_problem_IPhO_2026_3_C_4}

\paragraph{Problem source.}
The paramagnetic torus executes the Carnot refrigeration cycle
1 -> 2 -> 3 -> 4 -> 1 shown in Figure 3b in the H-versus-T plane.  T\_h and T\_c
are the hot- and cold-reservoir temperatures; Q\_h is the magnitude of heat
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
  \lean{IPhO2026Problems.IPhO2026_3_C_4.elapsed_time_formula}
  \uses{def:physics:IPhO_2026_3_C_4:aux001, def:physics:IPhO_2026_3_C_4:aux002, def:physics:IPhO_2026_3_C_4:aux003, def:physics:IPhO_2026_3_C_4:aux004, def:physics:IPhO_2026_3_C_4:aux005, def:physics:IPhO_2026_3_C_4:aux006, def:physics:IPhO_2026_3_C_4:aux007, def:physics:IPhO_2026_3_C_4:aux008, def:physics:IPhO_2026_3_C_4:aux009, def:physics:IPhO_2026_3_C_4:aux010, def:physics:IPhO_2026_3_C_4:aux011, def:physics:IPhO_2026_3_C_4:aux012, def:physics:IPhO_2026_3_C_4:aux013, lem:physics:IPhO_2026_3_C_4:aux014}
  The required running time for cooling the body from T₀ to T with constant heat capacity, constant refrigerator input power, and constant hot-reservoir temp
... [suffix omitted]
```

## 22. `IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`

- Open placeholders: 1
- Proof Review: new; attempts=0
- Review reason: (none)
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex`

### Lean excerpt
```lean
... [prefix omitted]
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
```

### Blueprint excerpt
```tex
... [prefix omitted]
and T\_c
are the hot- and cold-reservoir temperatures; Q\_h is the magnitude of heat
delivered to the hot reservoir and Q\_c is the magnitude absorbed from the cold
reservoir.  The equation of state is T*M*V = n*K*H and the isothermal heat
relation from part B may be reused.

Current subquestion:
Determine the overall coefficient of performance COP = Q\_c/W for all cycles up to the time found in C4.

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
  \lean{IPhO2026_3_C_5.overall_coefficient_of_performance}
  \uses{def:physics:IPhO_2026_3_C_5:aux001, def:physics:IPhO_2026_3_C_5:aux002, def:physics:IPhO_2026_3_C_5:aux003, def:physics:IPhO_2026_3_C_5:aux004, def:physics:IPhO_2026_3_C_5:aux005, def:physics:IPhO_2026_3_C_5:aux006, def:physics:IPhO_2026_3_C_5:aux007, def:physics:IPhO_2026_3_C_5:aux008, def:physics:IPhO_2026_3_C_5:aux009, def:physics:IPhO_2026_3_C_5:aux010, def:physics:IPhO_2026_3_C_5:aux011, def:physics:IPhO_2026_3_C_5:aux012, def:physics:IPhO_2026_3_C_5:aux013, def:physics:IPhO_2026_3_C_5:aux014, def:physics:IPhO_2026_3_C_5:aux015, def:physics:IPhO_2026_3_C_5:aux016, def:physics:IPhO_2026_3_C_5:aux017, def:physics:IPhO_2026_3_C_5:aux018, def:physics:IPhO
... [suffix omitted]
```

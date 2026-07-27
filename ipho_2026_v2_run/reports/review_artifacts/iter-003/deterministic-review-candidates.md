# Deterministic Review Candidate Pack

Iteration: 003
Exact review target count: 22

Review only these targets. Direct Lean compilation was already run in
parallel by the orchestrator; use the recorded result instead of rerunning it.

## 1. `IPhO2026Problems/problem_IPhO_2026_1_A_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 9.397
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_A_1.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_A_1.md`

### Lean excerpt
```lean
actor :
      0 < gate.gravitationalAcceleration.val *
        gate.geometry.sideLength.val ^ 3 :=
    mul_pos hLaws.gravitationalAcceleration_pos
      (pow_pos hFigure.sideLength_pos 3)
  have hDensityDiff :
      0 < gate.blockDensity.val - gate.waterDensity.val :=
    sub_pos.mpr hLaws.blockDensity_gt_water
  field_simp
  nlinarith

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
  rw [side_length_from_hydrostatic_balance gate hFigure hLaws hCritical,
    hDensity]
  have hrho : gate.waterDensity.val ≠ 0 :=
    ne_of_gt hLaws.waterDensity_pos
  field_simp
  ring

/--
The exact value obtained from `Δh = 1.41 m` is within half of one hundredth
of `0.50 m`, so `0.50 m` is the correct two-decimal report.
-/
lemma stated_value_rounds_to_half_meter :
    |(1.41 : ℝ) / (2 * Real.sqrt 2) - 0.50| < 0.005 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  have hLowerSqrt : (141 : ℝ) / 101 < Real.sqrt 2 := by
    nlinarith [hsqrt_sq]
  have hUpperSqrt : Real.sqrt 2 < (47 : ℝ) / 33 := by
    nlinarith [hsqrt_sq]
  rw [abs_lt]
  constructor <;> field_simp <;> nlinarith

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
  constructor
  · exact side_length_for_triple_density gate hFigure hLaws hCritical
      hData.blockDensity_eq
  · rw [side_length_for_triple_density gate hFigure hLaws hCritical
        hData.blockDensity_eq, hData.maximumLevelDifference_eq]
    exact stated_value_rounds_to_half_meter

end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
lem:physics:IPhO_2026_1_A_1:aux018, lem:physics:IPhO_2026_1_A_1:aux019}
  The hydrostatic and torque equations determine the cube side in terms of the two densities and the level difference.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration side\_length\_for\_triple\_density]
  \label{lem:physics:IPhO_2026_1_A_1:aux021}
  \lean{IPhO2026Problems.HydrostaticGateA1.side_length_for_triple_density}
  \uses{def:physics:IPhO_2026_1_A_1:aux013, def:physics:IPhO_2026_1_A_1:aux014, def:physics:IPhO_2026_1_A_1:aux015, def:physics:IPhO_2026_1_A_1:aux016, lem:physics:IPhO_2026_1_A_1:aux018, lem:physics:IPhO_2026_1_A_1:aux019, lem:physics:IPhO_2026_1_A_1:aux020}
  For a block of density 3ρ₀, the general critical-balance formula simplifies to a = Δh / (2√2).
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration stated\_value\_rounds\_to\_half\_meter]
  \label{lem:physics:IPhO_2026_1_A_1:aux022}
  \lean{IPhO2026Problems.HydrostaticGateA1.stated_value_rounds_to_half_meter}
  \uses{lem:physics:IPhO_2026_1_A_1:aux018, lem:physics:IPhO_2026_1_A_1:aux019, lem:physics:IPhO_2026_1_A_1:aux020, lem:physics:IPhO_2026_1_A_1:aux021}
  The exact value obtained from Δh = 1.41 m is within half of one hundredth of 0.50 m, so 0.50 m is the correct two-decimal report.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_A_1.md`
```markdown
ve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.HydrostaticGate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.MatchesFigure1a`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.ObeysHydrostaticLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.HydrostaticGateA1.TorqueSense`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 2. `IPhO2026Problems/problem_IPhO_2026_1_B_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 9.683
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_1.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_1.md`

### Lean excerpt
```lean
velocity.val‖
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
  have hm : s.positron.mass.val ≠ 0 :=
    ne_of_gt laws.positron_mass_positive
  have he : s.chargeMagnitude.val ≠ 0 :=
    ne_of_gt laws.charge_magnitude_positive
  have hε : s.vacuumPermittivity.val ≠ 0 :=
    ne_of_gt laws.vacuum_permittivity_positive
  have hℏ : s.reducedPlanckConstant.val ≠ 0 :=
    ne_of_gt laws.reduced_planck_constant_positive
  have ha : s.bohrRadius.val ≠ 0 :=
    ne_of_gt laws.bohr_radius_positive
  have hr : s.maximumSeparation.val ≠ 0 :=
    ne_of_gt laws.maximum_separation_positive
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoulomb :
      s.coulombConstant.val * s.chargeMagnitude.val ^ 2 =
        s.reducedPlanckConstant.val ^ 2 /
          (s.positron.mass.val * s.bohrRadius.val) := by
    rw [laws.coulomb_constant_definition, laws.bohr_radius_definition]
    field_simp [hm, he, hε, hℏ, hπ]
  have henergy :
      turningPointEnergyReadout s s.initialSeparation =
        turningPointEnergyReadout s s.maximumSeparation :=
    laws.isolated_energy_at_initial_turning_point.symm.trans
      laws.isolated_energy_at_outer_turning_point
  simp only [turningPointEnergyReadout] at henergy
  rw [laws.positron_angular_momentum, laws.mu_eq_four,
    laws.initial_separation_is_one_hundred_bohr_radii, hcoulomb] at henergy
  have hbranch := laws.outer_turning_point_branch
  rw [laws.initial_separation_is_one_hundred_bohr_radii] at hbranch
  field_simp [hm, ha, hr] at henergy
  ring_nf at henergy
  nlinarith

end IPhO2026Problem1B1
... [leading content omitted]
```

### Blueprint excerpt
```tex
_2026_1_B_1:aux010}
  All named physical quantities used in the electron--positron model. The scalar fields are readouts in one fixed unit system, while their types retain their physical dimensions. mu is the dimensionless angular-momentum factor.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration turningPointEnergyReadout]
  \label{def:physics:IPhO_2026_1_B_1:aux012}
  \lean{IPhO2026Problem1B1.turningPointEnergyReadout}
  \uses{def:physics:IPhO_2026_1_B_1:aux001, def:physics:IPhO_2026_1_B_1:aux011}
  The classical effective energy of the pair at a radial turning point of separation r. For either particle, ℓ = m (r/2) v, so the two kinetic energies sum to 4 ℓ² / (m r²). The electrostatic potential energy of the opposite charges is -k e² / r.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration CoulombPairLaws]
  \label{def:physics:IPhO_2026_1_B_1:aux013}
  \lean{IPhO2026Problem1B1.CoulombPairLaws}
  \uses{def:physics:IPhO_2026_1_B_1:aux011, def:physics:IPhO_2026_1_B_1:aux012}
  The figure readouts and physical laws for the isolated classical Coulomb pair. The two energy equations are the usable mathematical consequences of the classical, non-relativistic, electrostatic-only, isolated-system assumptions. The final numerical value of maximumSeparation is deliberately not a field.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_1.md`
```markdown
2026Problem1B1.EnergyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.MassQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.ParticleState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.PositionQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.VacuumPermittivityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1B1.VelocityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 3. `IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 39.805
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_B_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_B_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_2.md`

### Lean excerpt
```lean
have hb := sin_quarter_bounds ((289638 : ℝ) / 1000000)
        (by norm_num) (by norm_num)
        (by norm_num [sl, err, z]) (by norm_num [su, err, z])
        (by norm_num [cl, err, z]) (by norm_num [cu, err, z])
        (by norm_num [cl, err, z])
      have hnumeric :
          Real.sin ((289638 : ℝ) / 1000000) < 2 / 7 := by
        calc
          Real.sin ((289638 : ℝ) / 1000000) ≤
              2 * (2 * su ((289638 : ℝ) / 1000000) *
                cu ((289638 : ℝ) / 1000000)) *
                (2 * cu ((289638 : ℝ) / 1000000) ^ 2 - 1) := hb.2
          _ < 2 / 7 := by norm_num [su, cu, err, z]
      exact hmono.trans_lt hnumeric
    have hsin_upper :
        2 / 7 < Real.sin (3321 * Real.pi / 36000) := by
      have harg :
          (289811 : ℝ) / 1000000 < 3321 * Real.pi / 36000 := by
        nlinarith [Real.pi_gt_d20]
      have hmono :
          Real.sin ((289811 : ℝ) / 1000000) ≤
            Real.sin (3321 * Real.pi / 36000) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
        · exact harg.le
      have hb := sin_quarter_bounds ((289811 : ℝ) / 1000000)
        (by norm_num) (by norm_num)
        (by norm_num [sl, err, z]) (by norm_num [su, err, z])
        (by norm_num [cl, err, z]) (by norm_num [cu, err, z])
        (by norm_num [cl, err, z])
      have hnumeric :
          2 / 7 < Real.sin ((289811 : ℝ) / 1000000) := by
        calc
          2 / 7 <
              2 * (2 * sl ((289811 : ℝ) / 1000000) *
                cl ((289811 : ℝ) / 1000000)) *
                (2 * cl ((289811 : ℝ) / 1000000) ^ 2 - 1) := by
                  norm_num [sl, cl, err, z]
          _ ≤ Real.sin ((289811 : ℝ) / 1000000) := hb.1
      exact hnumeric.trans_le hmono
    have harcsin_lower :
        3319 * Real.pi / 36000 < Real.arcsin (2 / 7) := by
      refine (Real.lt_arcsin_iff_sin_lt
        (x := 3319 * Real.pi / 36000) (y := 2 / 7) ?_ ?_).mpr ?_
      · constructor <;> nlinarith [Real.pi_pos, Real.pi_lt_d20]
      · norm_num
      · exact hsin_lower
    have harcsin_upper :
        Real.arcsin (2 / 7) < 3321 * Real.pi / 36000 := by
      refine (Real.arcsin_lt_iff_lt_sin
        (x := 2 / 7) (y := 3321 * Real.pi / 36000) ?_ ?_).mpr ?_
      · norm_num
      · constructor <;> nlinarith [Real.pi_pos, Real.pi_lt_d20]
      · exact hsin_upper
    rw [hexact, Real.arccos_eq_pi_div_two_sub_arcsin]
    unfold radiansToDegrees
    rw [abs_lt]
    constructor <;>
      field_simp [Real.pi_ne_zero] <;>
      nlinarith [Real.pi_pos, harcsin_lower, harcsin_upper]

end IPhO2026_1_B_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
:physics:IPhO_2026_1_B_2:aux027}
  The source constants, initial angular momentum, energy relation, and supplied eccentricity formula give eccentricity 7/2 when μ = 15/2.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration outgoing\_polar\_angle\_at\_mu\_fifteen\_halves]
  \label{lem:physics:IPhO_2026_1_B_2:aux029}
  \lean{IPhO2026_1_B_2.outgoing_polar_angle_at_mu_fifteen_halves}
  \uses{def:physics:IPhO_2026_1_B_2:aux010, def:physics:IPhO_2026_1_B_2:aux026, lem:physics:IPhO_2026_1_B_2:aux027, lem:physics:IPhO_2026_1_B_2:aux028}
  The outgoing branch therefore has polar angle arccos (2/7).
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration fig1b\_signed\_deflection\_from\_polar\_angle]
  \label{lem:physics:IPhO_2026_1_B_2:aux030}
  \lean{IPhO2026_1_B_2.fig1b_signed_deflection_from_polar_angle}
  \uses{def:physics:IPhO_2026_1_B_2:aux010, def:physics:IPhO_2026_1_B_2:aux024, def:physics:IPhO_2026_1_B_2:aux026, lem:physics:IPhO_2026_1_B_2:aux027, lem:physics:IPhO_2026_1_B_2:aux028, lem:physics:IPhO_2026_1_B_2:aux029}
  Fig. 1b puts the initial positron velocity along the positive horizontal axis, while the conic's polar zero-axis points downward. The radial outgoing limit therefore converts polar angle θ∞ into signed deflection θ∞ - π/2.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_B_2.lean.md`
```markdown
al.Angle`, then applies the figure orientation and oriented-angle
addition. The final rounding certificate uses the official exact angle,
Mathlib's 20-decimal bounds on `π`, and explicit quarter-angle sine
enclosures derived from `Real.sin_bound` and `Real.cos_bound`.

## Verification

- Lean LSP diagnostics: no errors.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_1_B_2.lean`: success;
  the only warning is that the frozen `hConicParameter` hypothesis is unused.
- Source scan: no `sorry`, `admit`, `sorryAx`, `native_decide`, or introduced
  `axiom`.
- Axiom verification of all five theorems reports either no axioms or only
  Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.
- The verifier's only source-pattern warning is the pre-existing
  `planeFinrank` local instance.
- The configured Lake library has no individual module target for this
  problem file; direct Lean compilation verifies the file.

## Blueprint readiness

The proof environments for all five theorems are ready for `\leanok`. Per
`.archon/AGENTS.md`, the prover left the blueprint unchanged; deterministic
`sync_leanok` owns those markers.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_B_2.md`
```markdown
tMulActionNNReal` (PhysLean)
- `MulAction` (Mathlib)
- `CarriesDimension` (PhysLean)
- `DimEnergy` (PhysLean)
- `Finset.addEnergy` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Electromagnetism.EMSystem.coulombConstant` (PhysLean)
- `LocallyConstant` (Mathlib)
- `Lean.ConstantInfo.toDeclaration!` (Mathlib)

## Local abstractions introduced

- `IPhO2026_1_B_2.CoulombScatteringLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_B_2.Plane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_B_2.QuantityKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_B_2.QuantityModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_B_2.ScatteringScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 4. `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 30.073
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_C_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_1.md`

### Lean excerpt
```lean
s angularFrequency - boundaryEnergy =
          parameters.reducedPlanckConstant * delta := by
      dsimp [angularFrequency, boundaryEnergy, threshold, photonEnergy]
      ring
    have hDeltaBound :
        delta ≤
          (1 - 2 * coefficient * boundaryEnergy) /
            (2 * coefficient * parameters.reducedPlanckConstant) :=
      min_le_right _ _
    have hSecondNegative :
        coefficient *
              (photonEnergy parameters angularFrequency + boundaryEnergy) -
            1 <
          0 := by
      have hScaled :
          coefficient * parameters.reducedPlanckConstant * delta ≤
            (1 - 2 * coefficient * boundaryEnergy) / 2 := by
        have hRaw :=
          (le_div_iff₀ (by positivity :
            0 < 2 * coefficient * parameters.reducedPlanckConstant)).1
            hDeltaBound
        nlinarith
      nlinarith
    have hProductNegative :
        (photonEnergy parameters angularFrequency - boundaryEnergy) *
              (coefficient *
                  (photonEnergy parameters angularFrequency + boundaryEnergy) -
                1) <
            0 :=
      mul_neg_of_pos_of_neg
        (by rw [hEnergyDifference]; positivity) hSecondNegative
    rw [← hFactorIdentity] at hProductNegative
    have hEnough :
        HasEnoughPhotonEnergy parameters theta angularFrequency := by
      rw [HasEnoughPhotonEnergy]
      split
      · rw [hMinimumFormula]
        linarith
      · rw [hMinimumFormula]
        linarith
    have hAllowed :
        KinematicallyAllowed parameters theta angularFrequency :=
      (kinematicallyAllowed_iff_hasEnoughPhotonEnergy
        (parameters := parameters) (theta := theta)
        (angularFrequency := angularFrequency)
        ⟨hPlanck, hMass, hGap, hSmall⟩ hThetaNonnegative hThetaAtMostPi
        hAngularFrequency).mpr hEnough
    exact ⟨angularFrequency, hAllowed, by
      dsimp [angularFrequency]
      linarith⟩

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
  exact isDissociationThreshold_unique hMinimum
    (minimumAngularFrequency_isDissociationThreshold parameters theta
      hParameters hThetaNonnegative hThetaAtMostPi)

end IPhO2026Problem1C1
... [leading content omitted]
```

### Blueprint excerpt
```tex
:IPhO_2026_1_C_1:aux018}
  The displayed expression is the lower root of the minimized energy equation.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration isDissociationThreshold\_unique]
  \label{lem:physics:IPhO_2026_1_C_1:aux022}
  \lean{IPhO2026Problem1C1.isDissociationThreshold_unique}
  \uses{def:physics:IPhO_2026_1_C_1:aux003, def:physics:IPhO_2026_1_C_1:aux015, lem:physics:IPhO_2026_1_C_1:aux016, lem:physics:IPhO_2026_1_C_1:aux017, lem:physics:IPhO_2026_1_C_1:aux018, lem:physics:IPhO_2026_1_C_1:aux021}
  An infimum threshold, when it exists, is unique.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration minimumAngularFrequency\_eq]
  \label{lem:physics:IPhO_2026_1_C_1:aux024}
  \lean{IPhO2026Problem1C1.minimumAngularFrequency_eq}
  \uses{def:physics:IPhO_2026_1_C_1:aux003, def:physics:IPhO_2026_1_C_1:aux005, def:physics:IPhO_2026_1_C_1:aux015, def:physics:IPhO_2026_1_C_1:aux020, lem:physics:IPhO_2026_1_C_1:aux016, lem:physics:IPhO_2026_1_C_1:aux017, lem:physics:IPhO_2026_1_C_1:aux018, lem:physics:IPhO_2026_1_C_1:aux021, lem:physics:IPhO_2026_1_C_1:aux022, thm:physics:IPhO_2026_1_C_1:target}
  Equivalent value form: any scalar already identified semantically as the minimum dissociation frequency equals the explicit expression.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_C_1.lean.md`
```markdown
rt:
  `reports/ipho_2026/problem_IPhO_2026_1_C_1.source.json`.
- Theorem: `IPhO2026Problem1C1.event_scalar_energy_balance`.
- Blocker: the theorem has no positivity/validity assumption on the parameters,
  so the quantity named `photonMomentumMagnitude` can be negative. The norm of
  the photon vector is then its absolute value, while
  `radialFragmentKineticEnergy` uses the signed scalar. The claimed identity is
  false in that case.
- Concrete counterexample: take `ℏ = -1`, `m = c = 1`, `ω = 1`, `θ = π`,
  ozone energy `0`, molecule energy `-13/4`, photon momentum `-e₀`, molecule
  momentum `e₀`, and atom momentum `-2e₀`. All event fields hold and the fragment
  kinetic energy is `9/4`, but the theorem's left side is `-1` while its right
  side is `-3`.
- Smallest statement change: add
  `0 ≤ photonMomentumMagnitude parameters angularFrequency` as a hypothesis.
  The physically natural project-level change is instead to add
  `(hParameters : parameters.Valid)`, which supplies strict positivity.

The retained partial proof first derives the valid scalar energy balance with
`fragmentKineticEnergy` and leaves only the invalid signed-magnitude geometric
conversion as the focused gap.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_1.md`
```markdown
em1C1.DissociationEvent`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.HasEnoughPhotonEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.IsDissociationThreshold`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.KinematicallyAllowed`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.MomentumPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.Parameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem1C1.Parameters.Valid`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 5. `IPhO2026Problems/problem_IPhO_2026_1_C_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 28.864
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_1_C_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_2.md`

### Lean excerpt
```lean
gle_readout]
    unfold effectiveThresholdAngle thresholdShapeFactor
    rw [min_eq_left (by linarith [Real.pi_pos])]
    rw [Real.sin_pi_div_six]
    norm_num
  have hamu :
      massSI atomicMassUnit =
        8302695333 / 5000000000000000000000000000000000000 := by
    norm_num [massSI, atomicMassUnit, toDimensionful_apply_apply]
  have hev :
      energySI DimEnergy.electronVolt =
        801088317 / 5000000000000000000000000000 := by
    norm_num [energySI, DimEnergy.electronVolt, toDimensionful_apply_apply]
  have hmSI :
      massSI setup.atomMass =
        16 * (8302695333 / 5000000000000000000000000000000000000) := by
    rw [massInAtomicMassUnits, hamu] at atom_mass_readout
    field_simp at atom_mass_readout
    linarith
  have hmass :
      restEnergyInElectronVolts setup.atomMass =
        62184086900064638790833951 / 4172334984375000 := by
    rw [restEnergyInElectronVolts, hmSI, hev]
    norm_num
  have hgap : energyInElectronVolts setup.energyGap = 11 / 10 := by
    norm_num at energy_gap_readout ⊢
    exact energy_gap_readout
  let x : ℝ := energyInElectronVolts setup.thresholdPhotonEnergy
  have hbalance := _previousPart.threshold_balance
  rw [hgap, hangle, hmass] at hbalance
  ring_nf at hbalance
  change
    x =
      11 / 10 +
        x ^ 2 * (1043083746093750 / 62184086900064638790833951)
    at hbalance
  have hxnonneg := _previousPart.threshold_energy_nonnegative
  change 0 ≤ x at hxnonneg
  have hlower := _previousPart.lower_root_selection
  rw [hangle, hmass] at hlower
  norm_num at hlower
  change
    x ≤ 62184086900064638790833951 / 2086167492187500
    at hlower
  have hprod :
      0 ≤
        (62184086900064638790833951 / 2086167492187500 - x) * x :=
    mul_nonneg (sub_nonneg.mpr hlower) hxnonneg
  have hxle : x ≤ 11 / 5 := by
    nlinarith [hprod]
  have hxge : 11 / 10 ≤ x := by
    nlinarith [sq_nonneg x]
  have hxsqCoarse : x ^ 2 ≤ (11 / 5 : ℝ) ^ 2 := by
    nlinarith
  have hxTight : x ≤ 11000000001 / 10000000000 := by
    nlinarith [hxsqCoarse]
  have hxsqLower : (11 / 10 : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith
  have hxsqUpper :
      x ^ 2 ≤ (11000000001 / 10000000000 : ℝ) ^ 2 := by
    nlinarith
  have hexcessLower : (2025e-14 : ℝ) ≤ x - 11 / 10 := by
    nlinarith [hxsqLower]
  have hexcessUpper : x - 11 / 10 ≤ (2035e-14 : ℝ) := by
    nlinarith [hxsqUpper]
  have hreq :
      requestedExcessEnergyInElectronVolts setup = x - 11 / 10 := by
    dsimp [x]
    rw [requestedExcessEnergyInElectronVolts,
      ← _laws.threshold_photon_energy, hgap]
    rfl
  rw [hreq, abs_le]
  constructor <;> nlinarith

end IPhO2026_1_C_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
inition}[Declaration thresholdShapeFactor]
  \label{def:physics:IPhO_2026_1_C_2:aux018}
  \lean{IPhO2026_1_C_2.thresholdShapeFactor}
  \uses{def:physics:IPhO_2026_1_C_2:aux017}
  The angular factor occurring after minimization over the fragment momentum.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration PreviousPartC1Threshold]
  \label{def:physics:IPhO_2026_1_C_2:aux019}
  \lean{IPhO2026_1_C_2.PreviousPartC1Threshold}
  \uses{def:physics:IPhO_2026_1_C_2:aux011, def:physics:IPhO_2026_1_C_2:aux013, def:physics:IPhO_2026_1_C_2:aux015, def:physics:IPhO_2026_1_C_2:aux017, def:physics:IPhO_2026_1_C_2:aux018}
  The reusable content of part C.1, stated as the energy-balance equation for the lower threshold root. It is equivalent to the energy-conserving closed form and also records the θ ≥ π/2 branch through effectiveThresholdAngle.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration requestedExcessEnergyInElectronVolts]
  \label{def:physics:IPhO_2026_1_C_2:aux020}
  \lean{IPhO2026_1_C_2.requestedExcessEnergyInElectronVolts}
  \uses{def:physics:IPhO_2026_1_C_2:aux006, def:physics:IPhO_2026_1_C_2:aux008, def:physics:IPhO_2026_1_C_2:aux009, def:physics:IPhO_2026_1_C_2:aux011, def:physics:IPhO_2026_1_C_2:aux015}
  The scalar electronvolt readout of the requested quantity ℏ ω\_min - ΔU.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_1_C_2.lean.md`
```markdown
blem_IPhO_2026_1_C_2.lean` with a proof of
`IPhO2026_1_C_2.threshold_excess_energy_rounds_to_official_value`.

## Proof summary

- Evaluated the angle branch at `π / 6`, obtaining the exact shape factor `3 / 2`.
- Reduced the atomic-mass-unit, electronvolt, and speed-of-light readouts to
  exact rationals, obtaining the atom rest energy
  `62184086900064638790833951 / 4172334984375000` eV.
- Rewrote the previous-part balance as the exact quadratic
  `x = 11/10 + x² * (1043083746093750 / 62184086900064638790833951)`.
- Used nonnegativity and `lower_root_selection` to exclude the large root, then
  bounded the small-root excess between `2.025e-11` and `2.035e-11` eV.
- Used `threshold_photon_energy` to identify that excess with
  `requestedExcessEnergyInElectronVolts`.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_1_C_2.lean` succeeds.
- Lean LSP diagnostics: none.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom check reports only standard Lean/Mathlib axioms:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The theorem proof is closed and ready for the deterministic `\leanok` sync.
No redraft is needed.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_2.md`
```markdown
erasing it to a bare scalar.
- `IPhO2026_1_C_2.DimAction`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.DimAngularFrequency`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.DimMass`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.DimMomentum`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.OzonePhotodissociation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.PreviousPartC1Threshold`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_1_C_2.SourceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 6. `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 14.822
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_A_1.md`

### Lean excerpt
```lean
e
limiting angle. -/
lemma limiting_first_impact_angle {mirror : HalfCylindricalMirror}
    {experiment : MultipleReflectionExperiment mirror} {N : ℕ}
    {xN : LengthQuantity} (hN : 0 < N)
    (limiting : LimitingRayWitness experiment N xN)
    (closure : RepeatedReflectionClosure experiment N xN limiting) :
    limiting.firstImpactPolarAngle =
      Real.pi / (2 * (N : ℝ) + 1) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hfactor_ne : 2 * (N : ℝ) + 1 ≠ 0 := by
    positivity
  apply (eq_div_iff hfactor_ne).2
  nlinarith [closure.angle_closure]

/-- The two angles occurring in the official sine and cosine answer forms are
complementary. -/
lemma official_answer_angles_complementary (N : ℕ) (hN : 0 < N) :
    Real.pi / 2 - Real.pi / (2 * (N : ℝ) + 1) =
      (2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have h2N1_ne : 2 * (N : ℝ) + 1 ≠ 0 := by
    positivity
  have h4N2_ne : 4 * (N : ℝ) + 2 ≠ 0 := by
    positivity
  field_simp [h2N1_ne, h4N2_ne]
  ring

/-- Trigonometric bridge between the two official closed forms.  The Mathlib
carrier for the complementary-angle step is `Real.sin_pi_div_two_sub`. -/
lemma official_sine_cosine_forms_agree (N : ℕ) (hN : 0 < N) :
    Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) =
      Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  rw [← official_answer_angles_complementary N hN]
  exact Real.sin_pi_div_two_sub _

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
  obtain ⟨limiting, geometry, closure⟩ :=
    laws.limiting_ray_geometry laws.obeys_specular_reflection
      N xN hN hThreshold
  have hcos := geometry.coordinate_eq_radius_mul_cos
  rw [limiting_first_impact_angle hN limiting closure] at hcos
  constructor
  · rw [official_sine_cosine_forms_agree N hN]
    exact hcos
  · exact hcos

end IPhO2026Problem2A1
... [leading content omitted]
```

### Blueprint excerpt
```tex
stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration limiting\_first\_impact\_angle]
  \label{lem:physics:IPhO_2026_2_A_1:aux013}
  \lean{IPhO2026Problem2A1.limiting_first_impact_angle}
  \uses{def:physics:IPhO_2026_2_A_1:aux003, def:physics:IPhO_2026_2_A_1:aux006, def:physics:IPhO_2026_2_A_1:aux009, def:physics:IPhO_2026_2_A_1:aux011}
  Algebraic bridge from the repeated-reflection closure to the unique limiting angle.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration official\_answer\_angles\_complementary]
  \label{lem:physics:IPhO_2026_2_A_1:aux014}
  \lean{IPhO2026Problem2A1.official_answer_angles_complementary}
  \uses{lem:physics:IPhO_2026_2_A_1:aux013}
  The two angles occurring in the official sine and cosine answer forms are complementary.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration official\_sine\_cosine\_forms\_agree]
  \label{lem:physics:IPhO_2026_2_A_1:aux015}
  \lean{IPhO2026Problem2A1.official_sine_cosine_forms_agree}
  \uses{lem:physics:IPhO_2026_2_A_1:aux013, lem:physics:IPhO_2026_2_A_1:aux014}
  Trigonometric bridge between the two official closed forms. The Mathlib carrier for the complementary-angle step is Real.sin\_pi\_div\_two\_sub.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_A_1.lean.md`
```markdown
`IPhO2026Problems/problem_IPhO_2026_2_A_1.lean` without changing any
declaration signature:

- `IPhO2026Problem2A1.limiting_first_impact_angle`
- `IPhO2026Problem2A1.official_answer_angles_complementary`
- `IPhO2026Problem2A1.official_sine_cosine_forms_agree`
- `IPhO2026Problem2A1.positive_reflection_threshold_formula`

The final theorem obtains the limiting ray, projection equation, and angular
closure from `HalfCylinderReflectionLaws`; solves the closure algebraically;
and uses `Real.sin_pi_div_two_sub` to identify the official sine and cosine
forms.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_A_1.lean` succeeds with
  no errors or warnings.
- Source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- LSP axiom verification of
  `IPhO2026Problem2A1.positive_reflection_threshold_formula` reports only the
  standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The target theorem and all three auxiliary lemma proof environments are ready
for `\leanok`. Per prover write permissions, the blueprint chapter was left
unchanged for deterministic marker synchronization.

## Redraft needed

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_A_1.md`
```markdown
blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.LimitingRayWitness`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.MultipleReflectionExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.ObeysSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.OnReflectingSemicircle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.RepeatedReflectionClosure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2A1.SourceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 7. `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 20.374
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_B_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_1.md`

### Lean excerpt
```lean
alReflectedDirection, hInner,
    setup.sunlight_along_opticalAxis, hCenter]
  simp only [cross2D, canonicalOutwardNormal, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]
  rw [Real.sin_two_mul]
  linear_combination
    (setup.mirrorRadius.val * Real.sin theta * (1 - Real.cos theta)) *
      hOrientation

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
  have hAlphaVal : alpha.val = setup.mirrorRadius.val := by
    have h := coefficientIdentity (Real.pi / 2)
    rw [limitingRadiusMeters_eq_trigFormula] at h
    have hTwo : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [Real.sin_pi_div_two, hTwo, Real.sin_pi] at h
    simpa using h
  have hBetaVal :
      beta.val = (scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius).val := by
    have h := coefficientIdentity (Real.pi / 4)
    rw [limitingRadiusMeters_eq_trigFormula] at h
    have hTwo : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [hTwo, Real.sin_pi_div_two, hAlphaVal] at h
    change beta.val = -(1 / 2 : ℝ) * setup.mirrorRadius.val
    linarith
  exact ⟨WithDim.ext alpha setup.mirrorRadius hAlphaVal,
    WithDim.ext beta (scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius) hBetaVal⟩

end

end IPhO2026_2_B_1

end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
ics:IPhO_2026_2_B_1:aux025, lem:physics:IPhO_2026_2_B_1:aux026}
  For the maximum-incidence ray in the ray model, the actual container radius equals the canonical limiting-radius readout.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration limitingRadiusMeters\_eq\_trigFormula]
  \label{lem:physics:IPhO_2026_2_B_1:aux028}
  \lean{IPhO2026Problems.IPhO2026_2_B_1.limitingRadiusMeters_eq_trigFormula}
  \uses{def:physics:IPhO_2026_2_B_1:aux010, def:physics:IPhO_2026_2_B_1:aux017, lem:physics:IPhO_2026_2_B_1:aux025, lem:physics:IPhO_2026_2_B_1:aux026, lem:physics:IPhO_2026_2_B_1:aux027}
  Expanding the canonical incidence point, specular-reflection equation, and center offset from Figure 2f gives the two-term trigonometric radius formula.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{definition}[Declaration AreTrigCoefficients]
  \label{def:physics:IPhO_2026_2_B_1:aux029}
  \lean{IPhO2026Problems.IPhO2026_2_B_1.AreTrigCoefficients}
  \uses{def:physics:IPhO_2026_2_B_1:aux003, def:physics:IPhO_2026_2_B_1:aux010, def:physics:IPhO_2026_2_B_1:aux017}
  alpha and beta are the two universal coefficients of the limiting-radius function, rather than two arbitrary unknowns satisfying one numerical equation. This functional reading is the coefficient-identification content of B.1.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_B_1.lean.md`
```markdown
sed all five `sorry` placeholders without changing any declaration signature:

- `maximum_incidence_ray_is_tangent`
- `limiting_tangent_radius_eq_signedDistance`
- `maximum_ray_containerRadius_eq_limitingRadius`
- `limitingRadiusMeters_eq_trigFormula`
- `coefficients_from_solar_cooker_geometry`

The tangency lemma derives equality of the positive radius and signed distance
from the unit-direction, orthogonality, boundary, and signed-branch fields.
The trigonometric lemma expands the canonical ray geometry using the setup's
center offset, orthogonality, unit optical axis, and oriented basis.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_1.lean` succeeded.
- `lake build IPhO2026Run` succeeded.
- Source scan found no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification of the final theorem reports only standard Mathlib
  foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

All five theorem/lemma proof environments listed above are ready for
`\leanok`. The blueprint was not edited because prover write permissions are
restricted to the assigned Lean file and this task-result file.

## Redraft needed

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_1.md`
```markdown
abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.OnHalfMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.Power`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.RayHitsContainer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.SolarCookerSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.SolarOpticsModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_B_1.SpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 8. `IPhO2026Problems/problem_IPhO_2026_2_B_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 7.903
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_2.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_2.md`

### Lean excerpt
```lean
fSetup Ray)
    (hGeometry : Figure2fGeometry s) (hPower : Figure2fPowerBalance s) :
    s.receivedPower.val / s.noMirrorPower.val =
      s.actualProjectedWidth.val / s.noMirrorProjectedWidth.val := by
  have hIrradiance_ne : s.solarIrradiance.val ≠ 0 :=
    ne_of_gt hPower.irradiance_pos
  have hAxialLength_ne : s.axialLength.val ≠ 0 :=
    ne_of_gt hGeometry.axial_length_pos
  have hNoMirrorWidth_ne : s.noMirrorProjectedWidth.val ≠ 0 := by
    rw [hPower.no_mirror_projected_width]
    exact mul_ne_zero (by norm_num) (ne_of_gt hGeometry.container_radius_pos)
  have hNoMirrorPower_ne : s.noMirrorPower.val ≠ 0 := by
    rw [hPower.no_mirror_power_balance]
    exact mul_ne_zero (mul_ne_zero hIrradiance_ne hNoMirrorWidth_ne)
      hAxialLength_ne
  apply (div_eq_div_iff hNoMirrorPower_ne hNoMirrorWidth_ne).2
  rw [hPower.actual_power_balance, hPower.no_mirror_power_balance]
  ring

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
  have hTheta_lt_pi : s.thetaMax < Real.pi :=
    hGeometry.thetaMax_lt_pi_div_two.trans
      (half_lt_self Real.pi_pos)
  have hSin_pos : 0 < Real.sin s.thetaMax :=
    Real.sin_pos_of_pos_of_lt_pi hGeometry.thetaMax_pos hTheta_lt_pi
  have hCommon_ne :
      2 * s.mirrorRadius.val * Real.sin s.thetaMax ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt hGeometry.mirror_radius_pos))
      (ne_of_gt hSin_pos)
  calc
    s.receivedPower.val / s.noMirrorPower.val =
        s.actualProjectedWidth.val / s.noMirrorProjectedWidth.val :=
      power_ratio_eq_projected_width_ratio s hGeometry hPower
    _ = (2 * s.mirrorRadius.val * Real.sin s.thetaMax) /
        (2 * (s.mirrorRadius.val * Real.sin s.thetaMax *
          (1 - Real.cos s.thetaMax))) := by
      rw [hPower.actual_projected_width, hPower.no_mirror_projected_width,
        container_radius_factorization s hB1]
    _ = (2 * s.mirrorRadius.val * Real.sin s.thetaMax) /
        ((2 * s.mirrorRadius.val * Real.sin s.thetaMax) *
          (1 - Real.cos s.thetaMax)) := by
      congr 1
      ring
    _ = 1 / (1 - Real.cos s.thetaMax) := by
      simpa only [mul_one] using
        (mul_div_mul_left (1 : ℝ) (1 - Real.cos s.thetaMax) hCommon_ne)

end IPhO_2026_2_B_2
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
wer accounting for constant uniform irradiance. The two width equations are the Figure 2f projected-aperture readouts. The two power equations state that a fully absorbed parallel beam carries irradiance times projected area, with the common projected area written as width times axial length. None of these fields states the requested final ratio.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration container\_radius\_factorization]
  \label{lem:physics:IPhO_2026_2_B_2:aux011}
  \lean{IPhO2026Problems.IPhO_2026_2_B_2.container_radius_factorization}
  \uses{def:physics:IPhO_2026_2_B_2:aux006, def:physics:IPhO_2026_2_B_2:aux008}
  Part B.1 and the double-angle identity rewrite the container radius in a form that displays the factor which will cancel against the collected aperture.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration power\_ratio\_eq\_projected\_width\_ratio]
  \label{lem:physics:IPhO_2026_2_B_2:aux012}
  \lean{IPhO2026Problems.IPhO_2026_2_B_2.power_ratio_eq_projected_width_ratio}
  \uses{def:physics:IPhO_2026_2_B_2:aux006, def:physics:IPhO_2026_2_B_2:aux007, def:physics:IPhO_2026_2_B_2:aux010, lem:physics:IPhO_2026_2_B_2:aux011}
  The common irradiance and axial extent cancel, so the power ratio equals the ratio of the two projected widths.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_2.md`
```markdown
reserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.Figure2fSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.IrradianceReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.LengthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.PowerReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.PreviousPartB1Result`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO_2026_2_B_2.ValidFigure2fRayOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 9. `IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 8.334
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_B_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_3.md`

### Lean excerpt
```lean
fivefold_power
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
  have hcos : Real.cos cooker.thetaMax = (4 : ℝ) / 5 :=
    cosine_thetaMax_of_fivefold_power cooker actualPower baselinePower previous
      baselinePower_positive fivefold_power
  have htheta_le_pi : cooker.thetaMax ≤ Real.pi := by
    nlinarith [figure.thetaMax_le_pi_div_two, Real.pi_pos]
  have hsin_nonneg : 0 ≤ Real.sin cooker.thetaMax :=
    Real.sin_nonneg_of_nonneg_of_le_pi figure.thetaMax_nonnegative htheta_le_pi
  have htrig := Real.sin_sq_add_cos_sq cooker.thetaMax
  have hsin : Real.sin cooker.thetaMax = (3 : ℝ) / 5 := by
    rw [hcos] at htrig
    nlinarith
  have hsin_two : Real.sin (2 * cooker.thetaMax) = (24 : ℝ) / 25 := by
    rw [Real.sin_two_mul, hsin, hcos]
    norm_num
  have hradius := previous.radius_from_cutoff_ray
  rw [mirrorRadius_eq_one_metre, hsin, hsin_two] at hradius
  constructor
  · norm_num at hradius ⊢
    exact hradius
  · rw [lengthInCentimetres, hradius]
    norm_num

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
  constructor
  · exact
      cosine_thetaMax_of_fivefold_power cooker actualPower baselinePower previous
        baselinePower_positive fivefold_power
  · exact
      container_radius_of_fivefold_power cooker actualPower baselinePower figure previous
        mirrorRadius_eq_one_metre baselinePower_positive fivefold_power

end

end IPhO2026Problem2B3
... [leading content omitted]
```

### Blueprint excerpt
```tex
is the Figure 2f cutoff-ray geometry. The second is the received-power law for uniform parallel illumination and a fully absorbing container in the one-reflection regime.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration cosine\_thetaMax\_of\_fivefold\_power]
  \label{lem:physics:IPhO_2026_2_B_3:aux013}
  \lean{IPhO2026Problem2B3.cosine_thetaMax_of_fivefold_power}
  \uses{def:physics:IPhO_2026_2_B_3:aux004, def:physics:IPhO_2026_2_B_3:aux008, def:physics:IPhO_2026_2_B_3:aux010, def:physics:IPhO_2026_2_B_3:aux012}
  At a fivefold power gain over a positive baseline, the B.2 power law forces cos θ\_max = 4/5.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration container\_radius\_of\_fivefold\_power]
  \label{lem:physics:IPhO_2026_2_B_3:aux014}
  \lean{IPhO2026Problem2B3.container_radius_of_fivefold_power}
  \uses{def:physics:IPhO_2026_2_B_3:aux004, def:physics:IPhO_2026_2_B_3:aux006, def:physics:IPhO_2026_2_B_3:aux007, def:physics:IPhO_2026_2_B_3:aux008, def:physics:IPhO_2026_2_B_3:aux010, def:physics:IPhO_2026_2_B_3:aux011, def:physics:IPhO_2026_2_B_3:aux012, lem:physics:IPhO_2026_2_B_3:aux013}
  Using both previous-part laws and the nonnegative incidence-angle branch, R = 1 m together with a fivefold power gain forces the requested container radius.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_B_3.lean.md`
```markdown
nterval
`0 ≤ θ_max ≤ π/2` to select the nonnegative sine branch, derives
`sin θ_max = 3/5` from `sin² θ + cos² θ = 1`, evaluates
`sin (2 θ_max) = 24/25`, and substitutes these values into the B.1 cutoff-ray
geometry. The centimetre conclusion follows from the definition
`lengthInCentimetres x = 100 * lengthInMetres x`.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_B_3.lean`: success.
- Lean LSP diagnostics: none.
- Source scan: no `sorry`, `admit`, `sorryAx`, `native_decide`, or introduced
  `axiom`.
- Axiom check for the final theorem reports only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound`.
- The configured Lake library has no individual target named
  `IPhO2026Problems.problem_IPhO_2026_2_B_3`; direct compilation in the Lake
  environment was therefore used for module verification.

## Blueprint readiness

The proof environments for the two auxiliary theorems and the final target are
ready for `\leanok`. Per `.archon/AGENTS.md`, the prover did not edit the
blueprint; deterministic `sync_leanok` owns these markers.

## Needs blueprint entry

None. No declarations were added.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_3.md`
```markdown
DimArea.acre_in_SI` (PhysLean)
- `DimArea.hectare_in_SI` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problem2B3.Figure2fAssumptions`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2B3.IrradianceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2B3.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2B3.PreviousPartResults`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2B3.RadiantPowerQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem2B3.SolarCooker`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 10. `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 8.689
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_1.md`

### Lean excerpt
```lean
ricalMirror) (incidenceAngle : ℝ)
    (interaction : Figure2gRayInteraction mirror incidenceAngle) :
    lengthInMetres interaction.bA =
      lengthInMetres mirror.radius / (2 * Real.cos incidenceAngle) := by
  have hline := interaction.hit_on_reflected_line
  change
    lengthInMetres interaction.hitPoint.y =
      interaction.reflectedLine.slope *
          lengthInMetres interaction.hitPoint.x +
        lengthInMetres interaction.reflectedLine.intercept
    at hline
  rw [interaction.hit_point_x_from_figure,
    interaction.hit_point_y_from_figure] at hline
  have hslope := reflected_line_slope mirror incidenceAngle interaction
  change
    interaction.reflectedLine.slope = Real.cot (2 * incidenceAngle)
    at hslope
  rw [hslope] at hline
  have hsin_pos : 0 < Real.sin incidenceAngle :=
    Real.sin_pos_of_pos_of_lt_pi interaction.incidenceAngle_pos
      (by nlinarith [interaction.incidenceAngle_lt_pi_div_two, Real.pi_pos])
  have hcos_pos : 0 < Real.cos incidenceAngle :=
    Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [interaction.incidenceAngle_pos, Real.pi_pos],
        interaction.incidenceAngle_lt_pi_div_two⟩
  have htrig :
      Real.cos incidenceAngle -
          Real.cot (2 * incidenceAngle) * Real.sin incidenceAngle =
        1 / (2 * Real.cos incidenceAngle) := by
    rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul]
    field_simp [ne_of_gt hsin_pos, ne_of_gt hcos_pos]
    ring
  change
    lengthInMetres interaction.reflectedLine.intercept =
      lengthInMetres mirror.radius / (2 * Real.cos incidenceAngle)
  calc
    lengthInMetres interaction.reflectedLine.intercept =
        lengthInMetres mirror.radius *
          (Real.cos incidenceAngle -
            Real.cot (2 * incidenceAngle) * Real.sin incidenceAngle) := by
      nlinarith [hline]
    _ = lengthInMetres mirror.radius *
          (1 / (2 * Real.cos incidenceAngle)) := by rw [htrig]
    _ = lengthInMetres mirror.radius /
          (2 * Real.cos incidenceAngle) := by ring

/-- **IPhO 2026, Problem 2, C.1.**  In the Figure 2g coordinate convention,
the reflected ray A has slope `cot (2 * theta)` and intercept
`R / (2 * cos theta)`. -/
theorem rayA_slope_and_intercept
    (mirror : HalfCylindricalMirror) (theta : ℝ)
    (setup : Figure2gCausticSetup mirror theta) :
    setup.rayA.mA = Real.cot (2 * theta) ∧
      lengthInMetres setup.rayA.bA =
        lengthInMetres mirror.radius / (2 * Real.cos theta) := by
  exact
    ⟨reflected_line_slope mirror theta setup.rayA,
      reflected_line_intercept mirror theta setup.rayA⟩

end

end IPhO2026_2_C_1
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
_specular\_law]
  \label{lem:physics:IPhO_2026_2_C_1:aux018}
  \lean{IPhO2026Problems.IPhO2026_2_C_1.reflected_direction_from_specular_law}
  \uses{def:physics:IPhO_2026_2_C_1:aux008, def:physics:IPhO_2026_2_C_1:aux014}
  The vector reflection law and Figure 2g orientation select the outgoing down-left branch and give its doubled-angle direction.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration reflected\_line\_slope]
  \label{lem:physics:IPhO_2026_2_C_1:aux019}
  \lean{IPhO2026Problems.IPhO2026_2_C_1.reflected_line_slope}
  \uses{def:physics:IPhO_2026_2_C_1:aux008, def:physics:IPhO_2026_2_C_1:aux014, def:physics:IPhO_2026_2_C_1:aux015, lem:physics:IPhO_2026_2_C_1:aux018}
  The direction equation of the reflected supporting line determines its dimensionless slope.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration reflected\_line\_intercept]
  \label{lem:physics:IPhO_2026_2_C_1:aux020}
  \lean{IPhO2026Problems.IPhO2026_2_C_1.reflected_line_intercept}
  \uses{def:physics:IPhO_2026_2_C_1:aux008, def:physics:IPhO_2026_2_C_1:aux014, def:physics:IPhO_2026_2_C_1:aux016, lem:physics:IPhO_2026_2_C_1:aux018, lem:physics:IPhO_2026_2_C_1:aux019}
  Incidence of the reflected line at the mirror hit point determines its length-valued intercept.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_1.lean.md`
```markdown
direction. The down-left branch proves
`sin (2 * incidenceAngle) ≠ 0`, allowing the supporting-line direction
equation to be solved for its slope. Substitution of the hit-point coordinates
and slope into line incidence, together with positivity of sine and cosine on
the stated angle interval, yields the dimensionful intercept readout.

## Verification

- Lean LSP diagnostics: no errors.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`: success.
- `lake build`: success.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification of the final theorem reports only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound`; the source scan emitted no
  warnings.
- The configured Lake library has no individual target named
  `IPhO2026Problems.problem_IPhO_2026_2_C_1`; direct compilation and the
  successful aggregate build verify the file.

## Blueprint readiness

The proof environments for all three auxiliary theorems and the final target
are ready for `\leanok`. Per `.archon/AGENTS.md`, the prover left the blueprint
unchanged; deterministic `sync_leanok` owns these markers.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_1.md`
```markdown
asing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.PlaneDirection.IsSpecularReflection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.PlaneDirection.IsUnit`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.PlanePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.SlopeInterceptLine`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.SlopeInterceptLine.Contains`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_1.SlopeInterceptLine.HasDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 11. `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 18.06
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_2.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_2.md`

### Lean excerpt
```lean
HasDerivAt
          (fun y : ℝ =>
            lengthSI mirror.radius / (2 * Real.cos (θ + y)))
          ((lengthSI mirror.radius / 2) *
            (-(-Real.sin (θ + x) * 1) / Real.cos (θ + x) ^ 2)) x := by
      apply htmp.congr_of_eventuallyEq
      filter_upwards [] with y
      simp [div_eq_mul_inv]
      ring
    apply hsame.congr_deriv
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hintercept_deriv_differentiable :
      DifferentiableAt ℝ
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) 0 := by
    rw [show
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) =
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            (Real.sin (θ + x) / Real.cos (θ + x))) by
      funext x
      rw [Real.tan_eq_sin_div_cos]]
    fun_prop (disch := aesop)
  have hintercept_taylor_raw :=
    second_order_of_eventually_hasDeriv
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)))
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
          Real.tan (θ + x))
      (deriv
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) 0)
      hintercept_deriv hintercept_deriv_differentiable.hasDerivAt
  have hintercept_taylor :
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)) -
          (lengthSI mirror.radius / (2 * Real.cos θ) *
            (1 + Real.tan θ * x)))
        =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) :=
    hintercept_taylor_raw.congr
      (fun x => by simp; ring)
      (fun _ => rfl)

  have hslope_eq :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        (rayB x).reflectedLine.slope = Real.cot (2 * (θ + x)) := by
    filter_upwards [hB_geometry, h_reflection] with x hx_geometry hx_reflection
    rw [slope_eq_of_specular_law hx_reflection, hx_geometry.2.1]
  have hintercept_eq :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        lengthSI (rayB x).reflectedLine.yIntercept =
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) := by
    filter_upwards [hB_geometry, h_reflection] with x hx_geometry hx_reflection
    rw [intercept_eq_of_specular_law hx_reflection, hx_geometry.2.1]

  constructor
  · exact hslope_taylor.congr'
      (by
        filter_upwards [hslope_eq] with x hx
        rw [hx])
      Filter.EventuallyEq.rfl
  · exact hintercept_taylor.congr'
      (by
        filter_upwards [hintercept_eq] with x hx
        rw [hx])
      Filter.EventuallyEq.rfl

end IPhO2026Problems.IPhO2026_2_C_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
nition}[Declaration SatisfiesHalfCylindricalSpecularLaw]
  \label{def:physics:IPhO_2026_2_C_2:aux013}
  \lean{IPhO2026Problems.IPhO2026_2_C_2.SatisfiesHalfCylindricalSpecularLaw}
  \uses{def:physics:IPhO_2026_2_C_2:aux006, def:physics:IPhO_2026_2_C_2:aux007}
  The exact coefficient consequence of specular reflection from the circular mirror at an arbitrary incidence angle. C.2 applies this governing law at θ + Δθ and then takes its first-order expansion.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration slope\_eq\_of\_specular\_law]
  \label{lem:physics:IPhO_2026_2_C_2:aux014}
  \lean{IPhO2026Problems.IPhO2026_2_C_2.slope_eq_of_specular_law}
  \uses{def:physics:IPhO_2026_2_C_2:aux006, def:physics:IPhO_2026_2_C_2:aux007, def:physics:IPhO_2026_2_C_2:aux013}
  The exact slope equation exposed by the circular-mirror reflection law.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration intercept\_eq\_of\_specular\_law]
  \label{lem:physics:IPhO_2026_2_C_2:aux015}
  \lean{IPhO2026Problems.IPhO2026_2_C_2.intercept_eq_of_specular_law}
  \uses{def:physics:IPhO_2026_2_C_2:aux006, def:physics:IPhO_2026_2_C_2:aux007, def:physics:IPhO_2026_2_C_2:aux013, lem:physics:IPhO_2026_2_C_2:aux014}
  The exact intercept equation exposed by the circular-mirror reflection law.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_2.md`
```markdown
role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.HaveParallelIncomingDirections`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.OnUpperSemicircle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.OpticalRay2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.Point2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.SatisfiesHalfCylindricalSpecularLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_2.SatisfiesPreviousPartC1`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 12. `IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 17.416
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_3.md`

### Lean excerpt
```lean
(𝓝[>] (0 : ℝ))
        (𝓝 (reflectedSlope θ * (R * Real.sin θ ^ 3) +
          reflectedIntercept R θ)) :=
    (tendsto_const_nhds.mul hX).add tendsto_const_nhds
  have hYLimit :
      reflectedSlope θ * (R * Real.sin θ ^ 3) + reflectedIntercept R θ =
        (R / 2) * Real.cos θ * (2 - Real.cos (2 * θ)) := by
    rw [reflectedSlope, reflectedIntercept, Real.cot_eq_cos_div_sin,
      Real.sin_two_mul]
    field_simp
    rw [Real.cos_two_mul]
    rw [show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ]]
    ring
  rw [hYLimit] at hYPre
  have tendsto_planarPoint
      {ι : Type} {l : Filter ι} {fx fy : ι → ℝ} {x y : ℝ}
      (hx : Tendsto fx l (𝓝 x)) (hy : Tendsto fy l (𝓝 y)) :
      Tendsto (fun z => planarPoint (fx z) (fy z)) l
        (𝓝 (planarPoint x y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hsum :
        Tendsto (fun z => (fx z - x) ^ 2 + (fy z - y) ^ 2) l (𝓝 0) := by
      convert ((hx.sub tendsto_const_nhds).pow 2).add
        ((hy.sub tendsto_const_nhds).pow 2) using 1
      all_goals norm_num
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    convert hsqrt using 1
    · funext z
      rw [Space.dist_eq]
      congr 1
      rw [Fin.sum_univ_two]
      congr 1
    · norm_num
  simpa only [supportIntersectionCandidate] using
    tendsto_planarPoint hX hYPre

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
  apply (supportIntersectionCandidate_tendsto R θ hθ).congr'
  have hlt :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < δMax :=
    (eventually_lt_nhds hδMax).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ hδmax
  exact (neighboringIntersection_eq_supportIntersectionCandidate model
    (intersection δ) (hIntersection δ hδ hδmax)).symm

end
end IPhO2026_2_C_3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
gIntersection\_eq\_supportIntersectionCandidate]
  \label{lem:physics:IPhO_2026_2_C_3:aux024}
  \lean{IPhO2026Problems.IPhO2026_2_C_3.neighboringIntersection_eq_supportIntersectionCandidate}
  \uses{def:physics:IPhO_2026_2_C_3:aux001, def:physics:IPhO_2026_2_C_3:aux015, def:physics:IPhO_2026_2_C_3:aux017, def:physics:IPhO_2026_2_C_3:aux022, lem:physics:IPhO_2026_2_C_3:aux005, lem:physics:IPhO_2026_2_C_3:aux006, lem:physics:IPhO_2026_2_C_3:aux016, lem:physics:IPhO_2026_2_C_3:aux021, lem:physics:IPhO_2026_2_C_3:aux023}
  Ray membership and the C.1 support-line law determine the finite neighboring-ray intersection uniquely.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration supportIntersectionCandidate\_tendsto]
  \label{lem:physics:IPhO_2026_2_C_3:aux025}
  \lean{IPhO2026Problems.IPhO2026_2_C_3.supportIntersectionCandidate_tendsto}
  \uses{def:physics:IPhO_2026_2_C_3:aux004, def:physics:IPhO_2026_2_C_3:aux009, def:physics:IPhO_2026_2_C_3:aux022, lem:physics:IPhO_2026_2_C_3:aux005, lem:physics:IPhO_2026_2_C_3:aux006, lem:physics:IPhO_2026_2_C_3:aux016, lem:physics:IPhO_2026_2_C_3:aux021, lem:physics:IPhO_2026_2_C_3:aux023, lem:physics:IPhO_2026_2_C_3:aux024}
  Pure analytic bridge: the intersections of the C.1 support lines tend to the displayed caustic point as the positive angular separation tends to zero. The proof obligation includes the trigonometric simplification of both coordinates.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_3.lean.md`
```markdown
e exact derivatives of the reflected-line slope and intercept, computes the
limit of their divided differences, simplifies it with the double-angle
identities, and lifts the two scalar coordinate limits to `Space 2`. Actual
membership in both reflected rays first identifies every sufficiently close
intersection with the unique support-line intersection candidate.

## Verification

- Lean LSP diagnostics: no errors.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_2_C_3.lean`: success.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification was run on all six completed theorems. It reports only
  Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`, with no
  source-scan warnings.

The sole compiler warning is that the frozen hypothesis `hAngleWindow` in the
final theorem is redundant for this proof: `hIntersection` already supplies
admissibility of each neighboring angle.

## Blueprint readiness

The proof environments for all six theorems are ready for `\leanok`. Per
`.archon/AGENTS.md`, the prover left the blueprint unchanged; deterministic
`sync_leanok` owns these markers.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_3.md`
```markdown
e instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.IsNeighboringReflectedIntersection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.LiesOnReflectedSupport`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.OnUpperSemicircularMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.OrientedRay2D`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.OrientedRay2D.Contains`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_3.PlanarPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 13. `IPhO2026Problems/problem_IPhO_2026_2_C_4.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 15.694
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_4.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_4.md`

### Lean excerpt
```lean
rw [model.previousPartC3.2 θ]
  have hY := hYexplicit.congr_left hYcoordinates
  have hsinSq : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ => (Real.sin θ) ^ 2) (fun θ => θ ^ 2) := by
    change Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (Real.sin ^ 2) (id ^ 2)
    exact (Real.isEquivalent_sin.mono inf_le_left).pow 2
  have hscaledSin : Asymptotics.IsEquivalent (𝓝[≠] (0 : ℝ))
      (fun θ =>
        ((3 : ℝ) / 4) * model.frame.radiusReadout * (Real.sin θ) ^ 2)
      (fun θ =>
        ((3 : ℝ) / 4) * model.frame.radiusReadout * θ ^ 2) := by
    exact
      (Asymptotics.IsEquivalent.refl
        (u := fun _ : ℝ =>
          ((3 : ℝ) / 4) * model.frame.radiusReadout)).mul hsinSq
  have hpowerCoordinates :
      (fun θ =>
        ((3 : ℝ) / 4) *
            Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3) *
          Real.rpow |model.causticXReadout θ| ((2 : ℝ) / 3)) =ᶠ[
          𝓝[≠] (0 : ℝ)]
        (fun θ =>
          ((3 : ℝ) / 4) * model.frame.radiusReadout *
            (Real.sin θ) ^ 2) := by
    filter_upwards [] with θ
    rw [model.previousPartC3.1 θ]
    rw [abs_mul, abs_of_pos model.frame.radiusReadout_pos, abs_pow]
    have hm :
        Real.rpow
            (model.frame.radiusReadout * |Real.sin θ| ^ 3)
            ((2 : ℝ) / 3) =
          Real.rpow model.frame.radiusReadout ((2 : ℝ) / 3) *
            Real.rpow (|Real.sin θ| ^ 3) ((2 : ℝ) / 3) := by
      change
        (model.frame.radiusReadout * |Real.sin θ| ^ 3) ^
            ((2 : ℝ) / 3) =
          model.frame.radiusReadout ^ ((2 : ℝ) / 3) *
            (|Real.sin θ| ^ 3) ^ ((2 : ℝ) / 3)
      exact
        Real.mul_rpow model.frame.radiusReadout_pos.le
          (pow_nonneg (abs_nonneg (Real.sin θ)) 3)
    have hRprod :
        Real.rpow model.frame.radiusReadout ((1 : ℝ) / 3) *
            Real.rpow model.frame.radiusReadout ((2 : ℝ) / 3) =
          model.frame.radiusReadout := by
      change
        model.frame.radiusReadout ^ ((1 : ℝ) / 3) *
            model.frame.radiusReadout ^ ((2 : ℝ) / 3) =
          model.frame.radiusReadout
      rw [← Real.rpow_add model.frame.radiusReadout_pos]
      norm_num
    have hs : 0 ≤ |Real.sin θ| := abs_nonneg _
    have hsprod :
        Real.rpow (|Real.sin θ| ^ 3) ((2 : ℝ) / 3) =
          (Real.sin θ) ^ 2 := by
      change
        (|Real.sin θ| ^ 3) ^ ((2 : ℝ) / 3) =
          (Real.sin θ) ^ 2
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hs]
      norm_num
    rw [hm, hsprod]
    nlinarith [hRprod]
  exact hY.trans (hscaledSin.congr_left hpowerCoordinates.symm).symm

end
end IPhO2026_2_C_4
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
ration CausticPowerLawParameters]
  \label{def:physics:IPhO_2026_2_C_4:aux012}
  \lean{IPhO2026Problems.IPhO2026_2_C_4.CausticPowerLawParameters}
  Candidate parameters for a leading small-angle power law Y\_c = v |X\_c|\textasciicircum{}(p/q) + u. uReadout is a length readout. vScaleReadout is the numerical coefficient in the selected length unit; for the answer p/q = 2/3, it has the associated dimensional role length\textasciicircum{}(1/3).
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration HasSmallAnglePowerLaw]
  \label{def:physics:IPhO_2026_2_C_4:aux013}
  \lean{IPhO2026Problems.IPhO2026_2_C_4.HasSmallAnglePowerLaw}
  \uses{def:physics:IPhO_2026_2_C_4:aux009, def:physics:IPhO_2026_2_C_4:aux012}
  The rigorous meaning of the source's small-angle normal form: after removing the vertical offset, the two sides are asymptotically equivalent as θ → 0 through nonzero angles. The exponent is required to be a reduced fraction.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration deltaThetaEventuallySmallerThanTheta]
  \label{lem:physics:IPhO_2026_2_C_4:aux014}
  \lean{IPhO2026Problems.IPhO2026_2_C_4.deltaThetaEventuallySmallerThanTheta}
  As Δθ → 0, every fixed nonzero θ eventually satisfies the source hierarchy |Δθ| < |θ|, the precise local content needed from Δθ ≪ θ.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_4.md`
```markdown
of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.Figure2gFrame`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.FormsNeighboringRayCaustic`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.HasPreviousPartC3Coordinates`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.HasSmallAnglePowerLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.ReflectedRayReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_2_C_4.SatisfiesFigure2gReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 14. `IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 14.579
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_A_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_1.md`

### Lean excerpt
```lean
r Ampèrian loop through the torus. -/
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
  have hvolume_pos : 0 < siValue torus.volume := by
    rw [torus.volume_eq_meanCircumference_mul_area]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) torus.meanRadius_pos)
      torus.crossSectionArea_pos
  apply (eq_div_iff (ne_of_gt hvolume_pos)).2
  unfold ToroidalAmpereLaw at _ampereLaw
  calc
    siValue state.fieldStrength * siValue torus.volume =
        siValue state.fieldStrength *
          (meanLoopLengthSI torus * siValue torus.crossSectionArea) := by
      rw [torus.volume_eq_meanCircumference_mul_area]
      rfl
    _ = (siValue state.fieldStrength * meanLoopLengthSI torus) *
          siValue torus.crossSectionArea := by ring
    _ = ((winding.turnCount : ℝ) * siValue winding.currentMagnitude) *
          siValue torus.crossSectionArea := by rw [_ampereLaw]

end IPhO2026Problems.IPhO2026_3_A_1
... [leading content omitted]
```

### Blueprint excerpt
```tex
vide the claimed data.
\end{proof}

\begin{definition}[Declaration meanLoopLengthSI]
  \label{def:physics:IPhO_2026_3_A_1:aux016}
  \lean{IPhO2026Problems.IPhO2026_3_A_1.meanLoopLengthSI}
  \uses{def:physics:IPhO_2026_3_A_1:aux009, def:physics:IPhO_2026_3_A_1:aux013}
  The length 2πR of the circular Ampèrian loop through the torus.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration ParamagneticConstitutiveLaw]
  \label{def:physics:IPhO_2026_3_A_1:aux017}
  \lean{IPhO2026Problems.IPhO2026_3_A_1.ParamagneticConstitutiveLaw}
  \uses{def:physics:IPhO_2026_3_A_1:aux007, def:physics:IPhO_2026_3_A_1:aux009, def:physics:IPhO_2026_3_A_1:aux015}
  The scalar consequence of B = μ₀ H + μ₀ M for the common toroidal direction. It is recorded as a governing law, not as a definition of any field.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration ToroidalAmpereLaw]
  \label{def:physics:IPhO_2026_3_A_1:aux018}
  \lean{IPhO2026Problems.IPhO2026_3_A_1.ToroidalAmpereLaw}
  \uses{def:physics:IPhO_2026_3_A_1:aux009, def:physics:IPhO_2026_3_A_1:aux013, def:physics:IPhO_2026_3_A_1:aux014, def:physics:IPhO_2026_3_A_1:aux015, def:physics:IPhO_2026_3_A_1:aux016}
  Ampère's circuital law reduced using the approximately uniform toroidal field: the circulation H (2πR) equals the enclosed free current N I.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_A_1.lean.md`
```markdown
e:

- `IPhO2026Problems.IPhO2026_3_A_1.fieldStrength_eq_turns_current_area_div_volume`

The proof derives positivity, hence nonzeroness, of the torus volume from
`R > 0`, `A > 0`, `Real.pi_pos`, and
`volume_eq_meanCircumference_mul_area`. It then clears the volume denominator,
substitutes `V = (2πR) A`, reassociates the products, and rewrites with
`ToroidalAmpereLaw`.

## Verification

- Lean LSP diagnostics: no errors or warnings.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_A_1.lean`: success.
- `lake build IPhO2026Run`: success.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification reports only Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`; the source scan emitted no warnings.
- The configured Lake library has no individual target named
  `IPhO2026Problems.problem_IPhO_2026_3_A_1`; direct compilation and the
  successful aggregate library build verify the file.

## Blueprint readiness

The target theorem's proof environment is ready for `\leanok`. Per
`.archon/AGENTS.md`, the prover left the blueprint unchanged; deterministic
`sync_leanok` owns the marker.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_1.md`
```markdown
ing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.MagneticFluxDensityMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.MagneticPermeabilityMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ParamagneticConstitutiveLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.ToroidalAmpereLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.UniformToroidalMagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_A_1.VolumeMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 15. `IPhO2026Problems/problem_IPhO_2026_3_A_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 14.169
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_2.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_2.md`

### Lean excerpt
```lean
nsion ℝ
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
  rw [change.sourcePowerWorkLaw, change.externalSourceFaradayLaw,
    change.denseWindingFluxLinkageLaw, change.fluxPerTurnLaw]
  ring

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
  calc
    change.sourceWork.amount.val =
        winding.current.val * (winding.turns : ℝ) *
          geometry.crossSectionArea.val * change.fluxDensityChange.val :=
      source_work_eq_current_turns_area_dB geometry winding state change
    _ = geometry.volume.val * state.fieldStrength.val *
        change.fluxDensityChange.val := by
      rw [state.previousPartFieldMagnitude]
      field_simp [ne_of_gt geometry.volume_pos]

end IPhO2026Problems.Problem3A2
... [leading content omitted]
```

### Blueprint excerpt
```tex
yped definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration InfinitesimalMagneticChange]
  \label{def:physics:IPhO_2026_3_A_2:aux016}
  \lean{IPhO2026Problems.Problem3A2.InfinitesimalMagneticChange}
  \uses{def:physics:IPhO_2026_3_A_2:aux005, def:physics:IPhO_2026_3_A_2:aux007, def:physics:IPhO_2026_3_A_2:aux008, def:physics:IPhO_2026_3_A_2:aux009, def:physics:IPhO_2026_3_A_2:aux010, def:physics:IPhO_2026_3_A_2:aux011, def:physics:IPhO_2026_3_A_2:aux012, def:physics:IPhO_2026_3_A_2:aux015}
  Infinitesimal change used in Part A.2. The three governing equations separate the dense-winding flux law, Faraday's law with the external-source polarity, and the electrical work law. Thus the requested closed form is not assumed. The zero wire-heating equation records the negligible-resistance approximation from the apparatus description.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration source\_work\_eq\_current\_turns\_area\_dB]
  \label{lem:physics:IPhO_2026_3_A_2:aux017}
  \lean{IPhO2026Problems.Problem3A2.source_work_eq_current_turns_area_dB}
  \uses{def:physics:IPhO_2026_3_A_2:aux009, def:physics:IPhO_2026_3_A_2:aux011, def:physics:IPhO_2026_3_A_2:aux012, def:physics:IPhO_2026_3_A_2:aux016}
  Faraday's law and the electrical work law give the intermediate expression dW\_emf = I N A dB, before using the result of Part A.1.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_2.md`
```markdown
physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.InfinitesimalMagneticChange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.SignConsistentEnergyTransfer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.SignedEnergyTransfer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.ThinToroidalGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.ToroidalOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A2.UniformParamagneticState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 16. `IPhO2026Problems/problem_IPhO_2026_3_A_3.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 8.596
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_A_3.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_3.md`

### Lean excerpt
```lean
hH + siValue data.magnetizationM)
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
  have hsplit := laws.sourceWorkSplit
  rw [laws.previousPartSourceWork, laws.vacuumCoreWorkLaw] at hsplit
  rw [laws.differentialConstitutiveLaw,
    laws.vacuumCoreIncrementLaw] at hsplit
  ring_nf at hsplit ⊢
  linarith

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
  apply dimensionful_ext_si
  rw [siValue_energyFromSI]
  exact materialWork_siValue_eq data changes works laws

end Problem3A3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
026Problems.Problem3A3.WorkIncrements}
  \uses{def:physics:IPhO_2026_3_A_3:aux009}
  Signed infinitesimal work transfers. Under the required convention, a positive value denotes energy entering the named recipient.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration Assumptions]
  \label{def:physics:IPhO_2026_3_A_3:aux019}
  \lean{IPhO2026Problems.Problem3A3.Assumptions}
  \uses{def:physics:IPhO_2026_3_A_3:aux010, def:physics:IPhO_2026_3_A_3:aux015, def:physics:IPhO_2026_3_A_3:aux016, def:physics:IPhO_2026_3_A_3:aux017, def:physics:IPhO_2026_3_A_3:aux018}
  All assumptions used to derive A.3. In particular, this interface contains the work decomposition and the vacuum comparison, but does not contain the requested formula for materialWorkdW.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration materialWork\_siValue\_eq]
  \label{lem:physics:IPhO_2026_3_A_3:aux020}
  \lean{IPhO2026Problems.Problem3A3.materialWork_siValue_eq}
  \uses{def:physics:IPhO_2026_3_A_3:aux010, def:physics:IPhO_2026_3_A_3:aux016, def:physics:IPhO_2026_3_A_3:aux017, def:physics:IPhO_2026_3_A_3:aux018, def:physics:IPhO_2026_3_A_3:aux019, lem:physics:IPhO_2026_3_A_3:aux012, lem:physics:IPhO_2026_3_A_3:aux013}
  Scalar bridge for the A.3 subtraction: the material-work value in joules is μ₀ V H dM.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_A_3.md`
```markdown
-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.ToroidalOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.TorusData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.VacuumPermeability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.WorkIncrements`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3A3.WorkSignConvention`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 17. `IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 10.571
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_B_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_1.md`

### Lean excerpt
```lean
e same signed formula
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
  let coefficient :=
    vacuumPermeability_SI * torus.amountMoles *
      torus.materialK_SI / (fixedTemperature : ℝ)
  have hheatDerivative :
      ∀ s,
        HasDerivAt
          (fun r => energyInJoules (process.heatEntering r))
          (-coefficient *
            (initialFieldStrength +
              s * (finalFieldStrength - initialFieldStrength)) *
            (finalFieldStrength - initialFieldStrength)) s := by
    intro s
    have hderivative := laws.heatHasDerivative s
    rw [heatRate_eq torus vacuumPermeability_SI fixedTemperature
      initialFieldStrength finalFieldStrength process temperature_pos laws s,
      laws.prescribedFieldSweep s] at hderivative
    simpa only [coefficient] using hderivative
  have hintegrable :
      IntervalIntegrable
        (fun s : ℝ =>
          -coefficient *
            (initialFieldStrength +
              s * (finalFieldStrength - initialFieldStrength)) *
            (finalFieldStrength - initialFieldStrength))
        MeasureTheory.volume 0 1 := by
    exact
      (by
        fun_prop :
        Continuous
          (fun s : ℝ =>
            -coefficient *
              (initialFieldStrength +
                s * (finalFieldStrength - initialFieldStrength)) *
              (finalFieldStrength - initialFieldStrength))).intervalIntegrable 0 1
  have hintegral :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hheatDerivative s) hintegrable
  unfold netHeatEnteringInJoules
  rw [← hintegral]
  norm_num [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]
  dsimp only [coefficient]
  field_simp [ne_of_gt temperature_pos]
  ring

end

end ProblemIPhO2026_3_B_1
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
\label{lem:physics:IPhO_2026_3_B_1:aux006}
  \lean{IPhO2026Problems.ProblemIPhO2026_3_B_1.internalEnergyRate_eq_zero}
  \uses{def:physics:IPhO_2026_3_B_1:aux002, def:physics:IPhO_2026_3_B_1:aux003, def:physics:IPhO_2026_3_B_1:aux005}
  Along an isothermal sweep, dU = C\_M dT forces the internal-energy rate to vanish.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration magnetizationRate\_eq]
  \label{lem:physics:IPhO_2026_3_B_1:aux007}
  \lean{IPhO2026Problems.ProblemIPhO2026_3_B_1.magnetizationRate_eq}
  \uses{def:physics:IPhO_2026_3_B_1:aux002, def:physics:IPhO_2026_3_B_1:aux003, def:physics:IPhO_2026_3_B_1:aux005, lem:physics:IPhO_2026_3_B_1:aux006}
  The equation of state and the oriented linear field sweep determine the magnetization rate.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}

\begin{lemma}[Declaration heatRate\_eq]
  \label{lem:physics:IPhO_2026_3_B_1:aux008}
  \lean{IPhO2026Problems.ProblemIPhO2026_3_B_1.heatRate_eq}
  \uses{def:physics:IPhO_2026_3_B_1:aux002, def:physics:IPhO_2026_3_B_1:aux003, def:physics:IPhO_2026_3_B_1:aux005, lem:physics:IPhO_2026_3_B_1:aux006, lem:physics:IPhO_2026_3_B_1:aux007}
  Combining the first law, isothermal internal-energy law, equation of state, and magnetic work law determines the instantaneous heat rate.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_B_1.lean.md`
```markdown
sothermal
sweep has zero temperature rate, hence zero internal-energy rate. It then
solves the equation of state for magnetization and differentiates the
prescribed affine field sweep. The magnetic work law and first-law sign
convention give the heat rate. Finally, the fundamental theorem of calculus
integrates that affine heat rate from sweep parameter `0` to `1`, yielding the
required signed difference of squares.

## Verification

- Lean LSP diagnostics: no errors; only the frozen endpoint-nonnegativity
  hypotheses are reported as unused.
- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_B_1.lean`: success.
- Source scan: no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification for the target reports only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound`; the source scan emitted no
  warnings.

## Blueprint readiness

The proof environments for `internalEnergyRate_eq_zero`,
`magnetizationRate_eq`, `heatRate_eq`, and `heat_transferred_into_torus` are
ready for `\leanok`. Per `.archon/AGENTS.md`, the prover left the blueprint
unchanged; deterministic `sync_leanok` owns those markers.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_1.md`
```markdown
`Electromagnetism.ElectromagneticPotential.time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.magneticFieldMatrix_space_deriv_eq_time_deriv` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.IsPlaneWave.magneticFieldMatrix_eq_magneticFunction` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `Mathlib.Tactic.TFAE.Parser.tfaeHaveDecl` (Mathlib)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.ProblemIPhO2026_3_B_1.IsothermalFieldSweep`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.ProblemIPhO2026_3_B_1.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.ProblemIPhO2026_3_B_1.SatisfiesIsothermalParamagneticTorusLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 18. `IPhO2026Problems/problem_IPhO_2026_3_B_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 17.721
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_B_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_B_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_2.md`

### Lean excerpt
```lean
* finalFieldStrength.val ^ 2) /
              (model.heatCapacityParameterSI.val
                + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
                  * initialFieldStrength.val ^ 2)) - 1) := by
  let Ai : ℝ :=
    model.heatCapacityParameterSI.val
      + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * initialFieldStrength.val ^ 2
  let Af : ℝ :=
    model.heatCapacityParameterSI.val
      + model.vacuumPermeabilitySI.val * model.curieConstantSI.val
        * finalFieldStrength.val ^ 2
  have hcoeff :
      0 < model.vacuumPermeabilitySI.val * model.curieConstantSI.val :=
    mul_pos model.vacuumPermeability_pos model.curieConstant_pos
  have hAi : 0 < Ai := by
    exact add_pos_of_pos_of_nonneg model.heatCapacityParameter_pos
      (mul_nonneg hcoeff.le (sq_nonneg initialFieldStrength.val))
  have hAf : 0 < Af := by
    exact add_pos_of_pos_of_nonneg model.heatCapacityParameter_pos
      (mul_nonneg hcoeff.le (sq_nonneg finalFieldStrength.val))
  have hzero : (0 : ℝ) ∈ processDomain := by
    simp [processDomain]
  have hone : (1 : ℝ) ∈ processDomain := by
    simp [processDomain]
  have hTi : 0 < initialTemperature.val := by
    simpa [hphysics.initial_temperature] using
      hphysics.temperature_positive 0 hzero
  have hTf : 0 < finalTemperature.val := by
    simpa [hphysics.final_temperature] using
      hphysics.temperature_positive 1 hone
  have hinvPath :=
    magnetothermal_invariant_constant model path initialTemperature
      finalTemperature initialFieldStrength finalFieldStrength hphysics 1 hone
  have hinv :
      finalTemperature.val ^ 2 / Af = initialTemperature.val ^ 2 / Ai := by
    simpa [magnetothermalInvariantSI, magnetothermalScaleSI, Ai, Af,
      hphysics.initial_temperature, hphysics.final_temperature,
      hphysics.initial_field_strength, hphysics.final_field_strength] using hinvPath
  change finalTemperature.val - initialTemperature.val =
    initialTemperature.val * (Real.sqrt (Af / Ai) - 1)
  have hratio : 0 ≤ Af / Ai := div_nonneg hAf.le hAi.le
  have hrel := hinv
  field_simp [ne_of_gt hAf, ne_of_gt hAi] at hrel
  have hsquare :
      (initialTemperature.val * Real.sqrt (Af / Ai)) ^ 2 =
        finalTemperature.val ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hratio]
    field_simp [ne_of_gt hAi]
    nlinarith
  have hrhs : 0 ≤ initialTemperature.val * Real.sqrt (Af / Ai) :=
    mul_nonneg hTi.le (Real.sqrt_nonneg _)
  have hroot :
      finalTemperature.val = initialTemperature.val * Real.sqrt (Af / Ai) := by
    nlinarith
  rw [hroot]
  ring

end IPhO2026Problems.IPhO2026_3_B_2
... [leading content omitted]
```

### Blueprint excerpt
```tex
022}
  \lean{IPhO2026Problems.IPhO2026_3_B_2.magnetothermalScaleSI}
  \uses{def:physics:IPhO_2026_3_B_2:aux017, def:physics:IPhO_2026_3_B_2:aux018}
  The positive energy-times-temperature scale occurring in the ODE.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration magnetothermalInvariantSI]
  \label{def:physics:IPhO_2026_3_B_2:aux023}
  \lean{IPhO2026Problems.IPhO2026_3_B_2.magnetothermalInvariantSI}
  \uses{def:physics:IPhO_2026_3_B_2:aux017, def:physics:IPhO_2026_3_B_2:aux018, def:physics:IPhO_2026_3_B_2:aux022}
  The path invariant obtained by separating the reduced ODE.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration magnetothermal\_invariant\_constant]
  \label{lem:physics:IPhO_2026_3_B_2:aux024}
  \lean{IPhO2026Problems.IPhO2026_3_B_2.magnetothermal_invariant_constant}
  \uses{def:physics:IPhO_2026_3_B_2:aux008, def:physics:IPhO_2026_3_B_2:aux011, def:physics:IPhO_2026_3_B_2:aux017, def:physics:IPhO_2026_3_B_2:aux018, def:physics:IPhO_2026_3_B_2:aux019, def:physics:IPhO_2026_3_B_2:aux020, def:physics:IPhO_2026_3_B_2:aux023, lem:physics:IPhO_2026_3_B_2:aux021}
  Along any admissible adiabatic path, T² / (λ + μ₀ K H²) is constant. Mathlib's derivative-zero-on-an-interval theorem can carry the final calculus step once the reduced ODE has been established.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_B_2.lean.md`
```markdown
scale,
  differentiated `T² / (λ + μ₀ K H²)`, reduced its derivative to zero with the ODE,
  and applied `constant_of_derivWithin_zero` on `[0,1]`.
- `adiabatic_temperature_change`: evaluated the invariant at both endpoints,
  cross-multiplied the positive scales, and used positive endpoint temperatures to
  select the nonnegative square-root branch.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_B_2.lean` succeeds with no
  diagnostics.
- `lake build` succeeds (`Build completed successfully`).
- Source scan finds no `sorry`, `admit`, `sorryAx`, or introduced `axiom`.
- Axiom verification of the final theorem reports only the standard foundational
  axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint marker readiness

The proof environments for
`IPhO2026Problems.IPhO2026_3_B_2.reduced_adiabatic_temperature_ode`,
`IPhO2026Problems.IPhO2026_3_B_2.magnetothermal_invariant_constant`, and
`IPhO2026Problems.IPhO2026_3_B_2.adiabatic_temperature_change` are ready for
`\leanok`. The prover did not edit the blueprint because the project-local role
instructions reserve marker synchronization for the deterministic sync phase.

## Redraft needed

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_B_2.md`
```markdown
stead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.MagneticFieldStrengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.MagnetizationQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.ParamagneticTorusModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.TemperatureQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.VacuumPermeabilityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_B_2.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 19. `IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 12.331
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_2.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_2.md`

### Lean excerpt
```lean
ycle.hotTemperature *
          siValue cycle.coldTemperature) *
        (magnetizationSI cycle .one ^ 2 -
          magnetizationSI cycle .four ^ 2) =
      (siValue cycle.torus.vacuumPermeability *
          siValue cycle.torus.volume ^ 2 *
          siValue cycle.hotTemperature *
          siValue cycle.coldTemperature) *
        (magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2) := by
    calc
      _ = siValue cycle.coldTemperature *
          (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2 *
            siValue cycle.heatToHot) := by rw [hh']; ring
      _ = (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2) *
            (siValue cycle.coldTemperature *
              siValue cycle.heatToHot) := by ring
      _ = (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2) *
            (siValue cycle.heatFromCold *
              siValue cycle.hotTemperature) := by
        linear_combination
          (cycle.torus.constituentCount *
            siValue cycle.torus.curieConstant * 2) * hb
      _ = siValue cycle.hotTemperature *
          (cycle.torus.constituentCount *
              siValue cycle.torus.curieConstant * 2 *
            siValue cycle.heatFromCold) := by ring
      _ = _ := by rw [hc']; ring
  exact mul_left_cancel₀
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (ne_of_gt cycle.torus.vacuumPermeability_pos)
          (pow_ne_zero 2 (ne_of_gt cycle.torus.volume_pos)))
        hhot)
      hcold)
    hscaled

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
  have hnonneg : 0 ≤ magnetizationSI cycle .one := by
    exact (cycle.state .one).magnetization_nonneg
  have hsquare :
      magnetizationSI cycle .one ^ 2 =
        magnetizationSI cycle .two ^ 2 -
          magnetizationSI cycle .three ^ 2 +
          magnetizationSI cycle .four ^ 2 := by
    nlinarith [magnetization_square_balance cycle laws]
  calc
    magnetizationSI cycle .one =
        Real.sqrt (magnetizationSI cycle .one ^ 2) :=
      (Real.sqrt_sq hnonneg).symm
    _ = _ := congrArg Real.sqrt hsquare

end

end IPhO2026Problem3C2
... [leading content omitted]
```

### Blueprint excerpt
```tex
ureSI}
  \uses{def:physics:IPhO_2026_3_C_2:aux014, def:physics:IPhO_2026_3_C_2:aux015, def:physics:IPhO_2026_3_C_2:aux023}
  SI temperature at a labeled cycle vertex.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration SatisfiesParamagneticCarnotLaws]
  \label{def:physics:IPhO_2026_3_C_2:aux027}
  \lean{IPhO2026Problem3C2.SatisfiesParamagneticCarnotLaws}
  \uses{def:physics:IPhO_2026_3_C_2:aux014, def:physics:IPhO_2026_3_C_2:aux015, def:physics:IPhO_2026_3_C_2:aux023, def:physics:IPhO_2026_3_C_2:aux024, def:physics:IPhO_2026_3_C_2:aux025, def:physics:IPhO_2026_3_C_2:aux026}
  The physical laws used in part C.2. The heat-law equations preserve the orientation and sign convention from part B.1: heat transferred *into* the torus is positive. Thus Q\_c is used on 2 → 3, while the signed heat into the torus on 4 → 1 is -Q\_h.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration magnetization\_square\_balance]
  \label{lem:physics:IPhO_2026_3_C_2:aux028}
  \lean{IPhO2026Problem3C2.magnetization_square_balance}
  \uses{def:physics:IPhO_2026_3_C_2:aux023, def:physics:IPhO_2026_3_C_2:aux024, def:physics:IPhO_2026_3_C_2:aux027}
  The algebraic square balance obtained by combining the equation of state, the two isothermal heat equations, and the reversible Carnot heat balance.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_2.md`
```markdown
oblem3C2.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.PhysicalQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.SatisfiesParamagneticCarnotLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.Temperature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.ThermodynamicState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.VacuumPermeability`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problem3C2.Volume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 20. `IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 16.357
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_3.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_3.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_3.md`

### Lean excerpt
```lean
change)
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
  have hQ :
      heats.absorbedFromCold.siValue =
        (40207118149 / 976562500000 : ℝ) * Real.pi := by
    rw [heatLaw.coldHeatEquation, readouts.standardVacuumPermeability,
      readouts.torusAmount, readouts.potassiumChromateCurieConstant,
      heatLaw.coldReservoirContact, readouts.heliumInitialTemperature,
      readouts.fieldAtThree, readouts.fieldAtTwo]
    ring
  have hQ_error :
      abs (heats.absorbedFromCold.siValue - 129 / 1000) ≤ 1 / 2000 := by
    rw [hQ, abs_le]
    constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4]
  have hcal := calorimetry.energyBalance
  rw [readouts.heliumDensity, readouts.heliumVolume,
    readouts.heliumSpecificHeatCapacity, readouts.heliumInitialTemperature] at hcal
  norm_num at hcal
  rcases (abs_le.mp hQ_error) with ⟨hQ_lower, hQ_upper⟩
  refine ⟨hQ_error, ?_, ?_⟩
  · rw [readouts.heliumInitialTemperature, abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

end Problem3C3
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
:aux004, def:physics:IPhO_2026_3_C_3:aux008}
  Reusable conclusion of previous part C.2, with the nonnegative square-root branch selected by the magnitude-valued magnetization readouts.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration CarnotIsothermalHeatLaw]
  \label{def:physics:IPhO_2026_3_C_3:aux018}
  \lean{IPhO2026Problems.Problem3C3.CarnotIsothermalHeatLaw}
  \uses{def:physics:IPhO_2026_3_C_3:aux004, def:physics:IPhO_2026_3_C_3:aux008, def:physics:IPhO_2026_3_C_3:aux011, def:physics:IPhO_2026_3_C_3:aux012}
  The B.1 isothermal heat law applied to the oriented cold and hot legs. Heat entering the torus is positive. Thus Q\_c is the positive heat entering on 2 → 3, while Q\_h is the positive magnitude of the heat leaving on 4 → 1.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration HeliumCalorimetryLaw]
  \label{def:physics:IPhO_2026_3_C_3:aux019}
  \lean{IPhO2026Problems.Problem3C3.HeliumCalorimetryLaw}
  \uses{def:physics:IPhO_2026_3_C_3:aux003, def:physics:IPhO_2026_3_C_3:aux004, def:physics:IPhO_2026_3_C_3:aux011, def:physics:IPhO_2026_3_C_3:aux012}
  Constant-density, constant-specific-heat calorimetry for the helium. The energy absorbed by the torus is removed from the helium. The inequality selects the cooling rather than heating orientation of the signed balance.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_3.lean.md`
```markdown
rtified
`Real.pi_gt_d4` and `Real.pi_lt_d4` bounds prove the requested
`0.129 ± 0.0005 J` envelope. The helium calorimetry law reduces exactly to
`Q_c = 13 * (1 - T_final)`, and linear arithmetic then proves both requested
temperature envelopes.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_C_3.lean`: success,
  with only unused-hypothesis linter warnings.
- `lake build`: success.
- Lean LSP diagnostics: no errors; only the same unused-hypothesis warnings.
- Source scan: no `sorry`, `admit`, `sorryAx`, `native_decide`, or introduced
  `axiom`.
- Axiom check reports only Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.
- The configured Lake library has no individual target named
  `IPhO2026Problems.problem_IPhO_2026_3_C_3`; direct compilation in the Lake
  environment and the successful full project build verify the module.

## Blueprint readiness

The proof environment for the final target is ready for `\leanok`. Per
`.archon/AGENTS.md`, the prover did not edit the blueprint; deterministic
`sync_leanok` owns this marker.

## Needs blueprint entry

None. No declarations were added.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_3.md`
```markdown
n; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.PreviousPartC2MagnetizationRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.RefrigerationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.SIQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.SuppliedReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.TorusStateReading`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.Problem3C3.TorusVolumeMassBalance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 21. `IPhO2026Problems/problem_IPhO_2026_3_C_4.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 10.757
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_4.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_4.md`

### Lean excerpt
```lean
:
      ContinuousOn F (Set.Icc 0 experiment.elapsedTime.val) := by
    intro τ hτ
    exact (hF_differentiableAt τ hτ).continuousAt.continuousWithinAt
  have hF_differentiable :
      DifferentiableOn ℝ F (Set.Ioo 0 experiment.elapsedTime.val) := by
    intro τ hτ
    exact
      (hF_differentiableAt τ (Set.Ioo_subset_Icc_self hτ)).differentiableWithinAt
  obtain ⟨c, hc, hmean⟩ :=
    exists_deriv_eq_slope F htime_pos hF_continuous hF_differentiable
  have hc_closed : c ∈ Set.Icc 0 experiment.elapsedTime.val :=
    Set.Ioo_subset_Icc_self hc
  have hθ_pos : 0 < θ c := by
    simpa [θ] using law.temperature_pos_on_run c hc_closed
  have hθ_differentiable : DifferentiableAt ℝ θ c := by
    simpa [θ] using law.temperatureReadout_differentiable c
  have hF_deriv :
      deriv F c =
        (experiment.heatCapacity.val *
            experiment.hotReservoirTemperature.val /
          experiment.inputPower.val) *
        (deriv θ c / θ c -
          deriv θ c / experiment.hotReservoirTemperature.val) := by
    have hθ_hasDeriv :
        HasDerivAt θ (deriv θ c) c :=
      hθ_differentiable.hasDerivAt
    have hcalculus :=
      ((hθ_hasDeriv.log (ne_of_gt hθ_pos)).sub
        (hθ_hasDeriv.div_const
          experiment.hotReservoirTemperature.val)).const_mul
        (experiment.heatCapacity.val *
          experiment.hotReservoirTemperature.val /
            experiment.inputPower.val)
    simpa [F] using hcalculus.deriv
  have hinstant :
      experiment.inputPower.val =
        experiment.heatCapacity.val *
          (experiment.hotReservoirTemperature.val / θ c - 1) *
          (-deriv θ c) := by
    simpa [θ] using
      instantaneous_cooling_power_equation experiment process law c hc_closed
  have hF_deriv_eq : deriv F c = -1 := by
    rw [hF_deriv]
    field_simp [ne_of_gt hθ_pos, ne_of_gt hhot_pos,
      ne_of_gt experiment.inputPower_pos] at hinstant ⊢
    nlinarith
  rw [hF_deriv_eq] at hmean
  have hF_difference :
      F 0 - F experiment.elapsedTime.val =
        experiment.elapsedTime.val := by
    field_simp [ne_of_gt htime_pos] at hmean
    linarith
  have hinitial_pos : 0 < experiment.initialTemperature.val :=
    lt_trans experiment.finalTemperature_pos
      experiment.finalTemperature_lt_initial
  rw [Real.log_div (ne_of_gt hinitial_pos)
    (ne_of_gt experiment.finalTemperature_pos)]
  dsimp [F, θ] at hF_difference
  rw [← WithDim.val_div_val, ← WithDim.val_div_val] at hF_difference
  rw [law.initial_condition, law.final_condition] at hF_difference
  convert hF_difference.symm using 1
  all_goals ring

end IPhO2026_3_C_4
end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
gin{definition}[Declaration CarnotCoolingProcess]
  \label{def:physics:IPhO_2026_3_C_4:aux012}
  \lean{IPhO2026Problems.IPhO2026_3_C_4.CarnotCoolingProcess}
  \uses{def:physics:IPhO_2026_3_C_4:aux002, def:physics:IPhO_2026_3_C_4:aux007}
  Time-dependent readouts for the body temperature and the magnitudes of the cold- and hot-side heat-transfer rates.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration SatisfiesCarnotCoolingLaw]
  \label{def:physics:IPhO_2026_3_C_4:aux013}
  \lean{IPhO2026Problems.IPhO2026_3_C_4.SatisfiesCarnotCoolingLaw}
  \uses{def:physics:IPhO_2026_3_C_4:aux011, def:physics:IPhO_2026_3_C_4:aux012}
  The governing laws for the continuously repeated Carnot cycles. The three last fields encode, respectively, dQ\_c / dQ\_h = T\_c / T\_h, dQ\_c = -C\_c dT\_c, and P = dQ\_h/dt - dQ\_c/dt.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{lemma}[Declaration instantaneous\_cooling\_power\_equation]
  \label{lem:physics:IPhO_2026_3_C_4:aux014}
  \lean{IPhO2026Problems.IPhO2026_3_C_4.instantaneous_cooling_power_equation}
  \uses{def:physics:IPhO_2026_3_C_4:aux011, def:physics:IPhO_2026_3_C_4:aux012, def:physics:IPhO_2026_3_C_4:aux013}
  Eliminating the cold- and hot-side heat rates gives the instantaneous cooling equation that will be integrated in elapsed\_time\_formula.
\end{lemma}
\begin{proof}
  Substitute the cited governing relations in order and use the stated positivity, orientation, and branch conditions to obtain the conclusion.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_4.md`
```markdown
rve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.ParamagneticTorusContext`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.PowerQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.SatisfiesCarnotCoolingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.TemperatureQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_4.VolumeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

## 22. `IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 9.279
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_3_C_5.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_5.md`

### Lean excerpt
```lean
_trans hTfTi hTiH)
  have hScale :
      0 <
        siValue run.bodyHeatCapacity *
            temperatureValue run.finalCycle.hotReservoirTemperature /
          siValue run.inputPower :=
    div_pos (mul_pos hC hHot) hP
  have hProduct :
      0 <
        (siValue run.bodyHeatCapacity *
              temperatureValue run.finalCycle.hotReservoirTemperature /
            siValue run.inputPower) *
          (Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
            (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) /
              temperatureValue run.finalCycle.hotReservoirTemperature) := by
    rw [← htime]
    exact ht
  have hBracket :
      0 <
        Real.log
            (temperatureValue run.initialBodyTemperature /
              temperatureValue run.finalBodyTemperature) -
          (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature) /
            temperatureValue run.finalCycle.hotReservoirTemperature :=
    pos_of_mul_pos_right hProduct hScale.le
  have hFactor :
      0 <
        temperatureValue run.finalCycle.hotReservoirTemperature /
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) *
            Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
          1 := by
    rw [show
      temperatureValue run.finalCycle.hotReservoirTemperature /
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) *
            Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
          1 =
        (temperatureValue run.finalCycle.hotReservoirTemperature /
            (temperatureValue run.initialBodyTemperature -
              temperatureValue run.finalBodyTemperature)) *
          (Real.log
              (temperatureValue run.initialBodyTemperature /
                temperatureValue run.finalBodyTemperature) -
              (temperatureValue run.initialBodyTemperature -
                temperatureValue run.finalBodyTemperature) /
              temperatureValue run.finalCycle.hotReservoirTemperature) by
      field_simp [hΔ.ne', hHot.ne']]
    exact mul_pos (div_pos hHot hΔ) hBracket
  field_simp [hΔ.ne', hHot.ne', hC.ne', hP.ne', hBracket.ne',
    hFactor.ne']

end IPhO2026_3_C_5
... [leading content omitted]
```

### Blueprint excerpt
```tex
_5:aux004, def:physics:IPhO_2026_3_C_5:aux014}
  All dimensionful data accumulated over the cycles performed up to time t.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration ConstantPowerCoolingLaws]
  \label{def:physics:IPhO_2026_3_C_5:aux019}
  \lean{IPhO2026_3_C_5.ConstantPowerCoolingLaws}
  \uses{def:physics:IPhO_2026_3_C_5:aux007, def:physics:IPhO_2026_3_C_5:aux008, def:physics:IPhO_2026_3_C_5:aux018}
  Governing constant-heat-capacity and constant-power relations for the run.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration C4ElapsedTimeResult]
  \label{def:physics:IPhO_2026_3_C_5:aux020}
  \lean{IPhO2026_3_C_5.C4ElapsedTimeResult}
  \uses{def:physics:IPhO_2026_3_C_5:aux007, def:physics:IPhO_2026_3_C_5:aux008, def:physics:IPhO_2026_3_C_5:aux018}
  The reusable elapsed-time conclusion of part C.4.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}

\begin{definition}[Declaration overallCoefficientOfPerformance]
  \label{def:physics:IPhO_2026_3_C_5:aux021}
  \lean{IPhO2026_3_C_5.overallCoefficientOfPerformance}
  \uses{def:physics:IPhO_2026_3_C_5:aux007, def:physics:IPhO_2026_3_C_5:aux018}
  The overall coefficient of performance, Q\_c / W, for the whole run.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
... [leading content omitted]
```

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_3_C_5.lean.md`
```markdown
performance`

The proof substitutes the constant-heat-capacity heat removal equation, the
constant-power work equation, and the C.4 elapsed-time result. Positivity of
the heat capacity, input power, elapsed time, and temperatures proves that the
C.4 logarithmic bracket and the final COP denominator are nonzero. The
remaining equality is then an exact field simplification.

The isothermal-cycle hypotheses are intentionally unused: the theorem's
whole-run heat and work equations already contain the physical information
needed for C.5.

## Verification

- `lake env lean IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`: success.
- Lean LSP diagnostics: none.
- Source scan: no `sorry`, `admit`, `sorryAx`, `native_decide`, or introduced
  `axiom`.
- Axiom check reports only Mathlib's standard `propext`,
  `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The proof environment for
`IPhO2026_3_C_5.overall_coefficient_of_performance` is ready for `\leanok`.
Per `.archon/AGENTS.md`, the prover did not edit the blueprint; deterministic
`sync_leanok` owns this marker.

## Needs blueprint entry

None. No declarations were added.

## Redraft needed

None.

## Remaining blockers

None.
... [leading content omitted]
```

### Report excerpt: `physics-grounding-IPhO2026Problems_problem_IPhO_2026_3_C_5.md`
```markdown
t to a bare scalar.
- `IPhO2026_3_C_5.DimPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.DimVolume`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.Figure3bCarnotCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.Figure3bCarnotLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.IsothermalHeatModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.IsothermalHeatRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026_3_C_5.ParamagneticTorus`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
... [leading content omitted]
```

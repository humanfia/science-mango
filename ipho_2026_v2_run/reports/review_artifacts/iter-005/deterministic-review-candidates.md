# Deterministic Review Candidate Pack

Iteration: 005
Exact review target count: 2

Review only these targets. Direct Lean compilation was already run in
parallel by the orchestrator; use the recorded result instead of rerunning it.

## 1. `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 24.291
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_1_C_1.md`

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

## 2. `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`

- Compile status: passed
- Open sorries: 0
- Direct-check seconds: 15.162
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_B_1.md`

### Lean excerpt
```lean
icalAxis -
            setup.mirrorRadius.val •
              (Real.sin theta • setup.transverseAxis +
                Real.cos theta • setup.opticalAxis) := by
        rw [setup.center_on_symmetry_plane]
  have hOrientation := setup.basis_orientation
  unfold cross2D at hOrientation
  rw [limitingRadiusMeters, canonicalReflectedDirection, hInner,
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

The coefficients are exhibited for the actual container-radius equation
derived from the attained maximum ray and the Figure 2f tangency law.  They
are not arbitrary unknowns inferred from a single underdetermined equation.
-/
theorem coefficients_from_solar_cooker_geometry
    (setup : SolarCookerSetup) (model : SolarOpticsModel setup)
    (tangencyLaw : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (thetaMax_is_maximum : IsMaximumIncidenceAngle model thetaMax) :
    ∃ alpha beta : Length,
      setup.containerRadius.val =
          alpha.val * Real.sin thetaMax + beta.val * Real.sin (2 * thetaMax) ∧
        alpha = setup.mirrorRadius ∧
        beta = scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius := by
  refine ⟨setup.mirrorRadius,
    scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius, ?_, rfl, rfl⟩
  calc
    setup.containerRadius.val =
        limitingRadiusMeters setup thetaMax :=
      maximum_ray_containerRadius_eq_limitingRadius
        model tangencyLaw thetaMax thetaMax_is_maximum
    _ = setup.mirrorRadius.val * Real.sin thetaMax -
          (setup.mirrorRadius.val / 2) * Real.sin (2 * thetaMax) :=
      limitingRadiusMeters_eq_trigFormula setup thetaMax
    _ = setup.mirrorRadius.val * Real.sin thetaMax +
          (scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius).val *
            Real.sin (2 * thetaMax) := by
      simp only [scaledLength]
      ring

end

end IPhO2026_2_B_1

end IPhO2026Problems
... [leading content omitted]
```

### Blueprint excerpt
```tex
lem:physics:IPhO_2026_2_B_1:aux026}
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
  An auxiliary functional notion saying that alpha and beta are universal
  coefficients of the limiting-radius function.  The final B.1 theorem does
  not assume this notion; it derives and exhibits the source coefficients
  from the maximum-ray geometry.
\end{definition}
\begin{proof}
  This is the typed definition of the stated physical carrier; its fields or defining equation provide the claimed data.
\end{proof}
% --- Archon physics formalization source end ---
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

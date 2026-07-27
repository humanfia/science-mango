# Deterministic Plan Candidate Pack

Iteration: 005
Exact objective count: 2

The loop has already selected and written these objectives. Do not scan
the rest of the corpus and do not replace, reorder, add, or remove targets.
Use the excerpts below only to write a concise per-target proof strategy.

## 1. `IPhO2026Problems/problem_IPhO_2026_1_C_1.lean`

- Open placeholders: 1
- Proof Review: retry; attempts=0
- Review reason: formalization redraft passed at iter 4; proof attempt budget reset
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_1_C_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
angularFrequency < threshold + epsilon

/--
Under the parameter-validity conditions, vector conservation and the
Figure 1c angle imply the scalar energy law.
-/
theorem event_scalar_energy_balance
    {parameters : Parameters} {theta angularFrequency : ℝ}
    (hParameters : parameters.Valid)
    (event : DissociationEvent parameters theta angularFrequency) :
    photonEnergy parameters angularFrequency =
      parameters.energyGap +
        radialFragmentKineticEnergy parameters theta angularFrequency
          ‖event.oxygenMoleculeMomentum‖ := by
  have hEnergy :
      photonEnergy parameters angularFrequency =
        parameters.energyGap +
          fragmentKineticEnergy parameters event.oxygenMoleculeMomentum
            event.oxygenAtomMomentum := by
    rw [Parameters.energyGap]
    linarith [event.energy_conservation]
  rw [hEnergy]
  congr 1
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hPhotonMomentum :
      0 < photonMomentumMagnitude parameters angularFrequency := by
    unfold photonMomentumMagnitude photonEnergy
    have hSpeed : 0 < parameters.speedOfLight.val :=
      parameters.speedOfLight.pos
    exact div_pos (mul_pos hPlanck event.angularFrequency_pos) hSpeed
  /-
  The remaining geometric identity uses `hPhotonMomentum` to remove the
  absolute value from the norm of the photon-momentum scalar multiple, then
  uses momentum conservation and the Figure 1c angle identity to evaluate the
  squared norm of the oxygen-atom momentum.
  -/
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
  rcases hParameters with ⟨hPlanck, hMass, hGap, hSmall⟩
  have hSpeed : 0 < parameters.speedOfLight.val :=
    parameters.speedOfLight.pos
  have hPhotonEnergy : 0 ≤ photonEnergy parameters angularFrequency := by
    unfold photonEnergy
    positivity
  have hPhotonMomentum :
      0 ≤ photonMomentumMagnitude parameters angularFrequency := by
    unfold photonMomentumMagnitude
    positivity
  by_cases hForward : theta ≤ Real.pi / 2
  · rw [minimumFragmentKineticEnergy, if_pos hForward]
    have hTrig := Real.sin_sq_add_cos_sq theta
    have hSquare :
        0 ≤
          (3 * r -
            2 * photonMomentumMagnitude parameters angularFrequency *
              Real.cos theta) ^ 2 := sq_nonneg _
    have hMinimum :
        photonMomentumMagnitude parameters angularFrequency ^ 2 *
              angularFactor theta /
            (6 * parameters.oxygenAtomMass) =
          (2 * photonMomentumMagnitude parameters angul
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

\paragraph{Iteration 004 proof-review redraft contract.}
The scalar event-balance lemma must assume the applicability conditions on the
physical parameters.  In particular, positivity of \(\hbar\), the photon
frequency, and \(c\) makes the quantity called the photon-momentum magnitude
nonnegative.  Do not assert the radial formula for arbitrary signed parameter
readouts.  Preserve the already established threshold expression and the
downstream theorem statements.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_1_C_1:target}
  \lean{IPhO2026Problem1C1.minimumAngularFrequency_isDissociationThreshold}
  \uses{def:physics:IPhO_2026_1_C_1:aux001, def:physics:IPhO_2026_1_C_1:aux002, def:physics:IPhO_2026_1_C_1:aux003, def:physics:IPhO_2026_1_C_1:aux004, def:physics:IPhO_2026_1_C_1:aux005
... [suffix omitted]
```

## 2. `IPhO2026Problems/problem_IPhO_2026_2_B_1.lean`

- Open placeholders: 0
- Proof Review: retry; attempts=0
- Review reason: formalization redraft passed at iter 4; proof attempt budget reset
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_B_1.tex`

### Lean excerpt
```lean
... [prefix omitted]
(Real.sin theta • setup.transverseAxis +
                  Real.cos theta • setup.opticalAxis)) =
          (setup.containerCenterMeters - setup.mirrorCenterMeters) -
            setup.mirrorRadius.val •
              (Real.sin theta • setup.transverseAxis +
                Real.cos theta • setup.opticalAxis) := by
        module
      _ = (setup.mirrorRadius.val / 2) • setup.opticalAxis -
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

\paragraph{Iteration 004 proof-review redraft contract.}
Do not assume that arbitrary \(\alpha,\beta\) already form the coefficients of
the full limiting-radius function.  Starting only from the solar-cooker setup,
the ray model, maximal-ray tangency, and the fact that
\(\theta_{\max}\) is the attained maximum, derive the actual container-radius
equation.  The final theorem must exhibit coefficients \(\alpha,\beta\) for
that derived equation and identify them as
\(\alpha=R\) and \(\beta=-R/2\).  Thus every load-bearing Figure 2f hypothesis
feeds the answer, rather than being decorative beside an answer-bearing
coefficient assumption.

\begin{theorem}[Physics formalization target]
  \label{thm:physics:IPhO_2026_2_B_1:target}
  \lean{IPhO2026Problems.IPhO2026_2_B_1.coefficients_from_solar_cooker_geometry}
  \uses
... [suffix omitted]
```

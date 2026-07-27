# Deterministic Review Candidate Pack

Iteration: 002
Exact review target count: 3

Review only these targets. Direct Lean compilation was already run in
parallel by the orchestrator; use the recorded result instead of rerunning it.

## 1. `IPhO2026Problems/problem_IPhO_2026_2_A_1.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 9.055
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_A_1.tex`
- Reports: `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_A_1.md`

### Lean excerpt
```lean
ng threshold produces both the
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

## 2. `IPhO2026Problems/problem_IPhO_2026_2_C_1.lean`

- Compile status: passed
- Open sorries: 4
- Direct-check seconds: 4.287
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_1.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_1.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_1.md`

### Lean excerpt
```lean
+ deltaTheta`, and intersects ray A's
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
rd normal, and a specular reflected supporting
  line.  The explicit local interface preserves exactly those missing roles.
- Mathlib's `EuclideanGeometry.reflection` reflects points across a fixed
  affine subspace.  It is not directly a direction-reflection law at the
  tangent of a curved mirror, so using it would require a larger geometric
  encoding than the source contract.
- No dedicated half-cylindrical-mirror/specular-optics API was found in the
  searched Mathlib/Physlib surface.
- `archon dag-query` was attempted exactly as instructed, but the executable
  was not available on this lane's `PATH`.  The blueprint declares no
  previous-part theorem dependency, so this did not block the contract.
- The source supplies no numeric interpretation of `Δθ ≪ θ`; the
  formalization therefore retains an explicit relative-scale witness rather
  than inventing a tolerance.

## Redraft requests

- None for the Lean contract.  A later plan/review pass may optionally assign
  separate blueprint labels to the new Physlib-grounded support declarations
  `LengthQuantity` and `lengthInMetres`; their absence from the current index
  does not affect compilation or the target theorem mapping.
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

## 3. `IPhO2026Problems/problem_IPhO_2026_2_C_2.lean`

- Compile status: passed
- Open sorries: 1
- Direct-check seconds: 8.724
- Blueprint: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_2.tex`
- Reports: `.archon/task_results/IPhO2026Problems_problem_IPhO_2026_2_C_2.lean.md`, `.archon/task_results/physics-grounding-IPhO2026Problems_problem_IPhO_2026_2_C_2.md`

### Lean excerpt
```lean
m the circular
mirror at an arbitrary incidence angle.  C.2 applies this governing law at
`θ + Δθ` and then takes its first-order expansion. -/
def SatisfiesHalfCylindricalSpecularLaw
    (mirror : HalfCylindricalMirror) (ray : OpticalRay2D) : Prop :=
  ray.reflectedLine.slope =
      Real.cot (2 * ray.incidenceAngle) ∧
    lengthSI ray.reflectedLine.yIntercept =
      lengthSI mirror.radius / (2 * Real.cos ray.incidenceAngle)

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
    lengthSI ray.reflectedLine.yIntercept =
      lengthSI mirror.radius / (2 * Real.cos ray.incidenceAngle) :=
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

### Report excerpt: `IPhO2026Problems_problem_IPhO_2026_2_C_2.lean.md`
```markdown
, `AffineLineReadout`, and `HalfCylindricalMirror` preserve the
  distinct physical roles of position, line coefficient, and mirror radius.
- `Direction2D` remains a dimensionless signed component model because only
  Figure 2g orientation and the slope ratio are required.
- `OpticalRay2D` and `Figure2gRayLabel` retain the ray identity, incidence
  point/angle, directions, and reflected line.
- The six local `Prop` interfaces listed in the countermodel audit expose all
  required mathematical constraints directly.

## Grounding gaps and redraft requests

- LeanExplore located no ready-made Physlib geometric-optics object or
  half-cylindrical specular-reflection law matching Figure 2g. The smallest
  faithful local ray, mirror, geometry, and exact-law interfaces remain
  necessary.
- Mathlib has generic analytic/Taylor machinery but no single theorem
  packaging these two exact trigonometric `O(Δθ²)` expansions. This is not a
  statement-level blocker; all required exact equations, nonsingularity
  conditions, and remainder targets are present.
- Blueprint redraft request: add dedicated definition blocks for
  `LengthQuantity` and `lengthSI`. No source-physics redraft is requested.
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

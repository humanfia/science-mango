# Autoformalization result: `problem_phyx_mini_0093.lean`

## Retry outcome

The iteration-001 review gate requested a direct Physlib/PhysLean import and
genuine use of the available physics library before local abstractions were
introduced. The redraft now imports `Physlib.Units.WithDim.Basic` and models
optical intensity as Physlib's dimension-tagged `WithDim (M / T^3) ℝ`, rather
than as a bare real number.

The chapter contains `% archon:physics`, so the physics-formalize discipline
was used. The primary image was inspected directly. It confirms an
unpolarized source of intensity `I₀`, a vertical first polarizer, a middle
polarizer at `60°`, a final polarizer at `90°`, and labeled beam points A, B,
and C. The recorded answer A (`I = 0`) agrees with the crossed `0°` and `90°`
axes left after removal of the middle filter.

## Assumption/target split

### Governing laws

- `PassesThroughIdealLinearPolarizer` states the generic ideal-polarizer
  transition law. Unpolarized incident light is halved; linearly polarized
  incident light obeys Malus's cosine-squared law; in both cases the outgoing
  polarization is aligned with the filter axis.
- `ThreePolarizerOpticsLaws.through_A`, `original_through_B`, and
  `original_through_C` apply that generic law to the displayed three-filter
  experiment.
- `ThreePolarizerOpticsLaws.without_B_through_C` applies the same generic law
  to the modified experiment from A directly through C. It does not assert
  that the outgoing intensity vanishes.
- `LightBeam.intensity_nonnegative` records the physical nonnegativity of
  every beam intensity.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the problem
  is standalone.

### Figure/data readouts

- `ThreePolarizerFigureReadouts.source_intensity` identifies the incident
  beam's dimensioned intensity with the pictured source label `I₀`.
- `source_unpolarized` records the pictured unpolarized input.
- `axis_A_vertical`, `axis_B_sixty_degrees`, and
  `axis_C_ninety_degrees` record the image readouts `0`, `π/3`, and `π/2`
  radians relative to the vertical reference.
- `ThreePolarizerSetup` retains all three filters and beams at A, B, and C,
  plus a distinct beam at C in the modified experiment with B removed.

### Current target conclusions

- `intensity_at_C_after_removing_middle_filter` concludes that the
  dimensioned intensity of `beamAtCWithoutB` is exactly zero, i.e. answer A.

## Goal-faithfulness audit

The zero-intensity answer occurs only in the theorem conclusion (apart from
documentation). `ThreePolarizerSetup.beamAtCWithoutB` is an unconstrained
physical beam; its intensity is deliberately not assigned by that structure.
The `without_B_through_C` law is a generic filter transition whose output
depends on the incoming beam, the outgoing beam, and the angular difference.
Only after combining it with the independent figure readouts for A and C can
one derive the target.

The source intensity `I₀` is arbitrary and is not assumed to be zero. Neither
the figure-readout structure nor the optics-law structure contains the target
equality. No `True`, reflexive equality, target-shaped local definition, or
premise field makes the theorem true by unfolding.

`OpticalIntensity` is not a scalar placeholder: it is Physlib's
`WithDim opticalIntensityDimension ℝ`, where the dimension is explicitly
`M/T³` (power per area). Bare reals are used only for fixed-unit scalar
readouts and dimensionless radian angles/transmittance factors. The theorem
itself equates the dimensioned physical intensity, rather than merely an
untyped scalar, to dimensioned zero.

## Declarations and blueprint correspondence

- Dimensional layer: `opticalIntensityDimension`, `OpticalIntensity`.
- Physical primitives: `PolarizationState`, `LightBeam`,
  `IdealLinearPolarizer`.
- Governing law: `PassesThroughIdealLinearPolarizer`.
- Scene and evidence: `ThreePolarizerSetup`,
  `ThreePolarizerFigureReadouts`, `ThreePolarizerOpticsLaws`.
- Target theorem: `intensity_at_C_after_removing_middle_filter` corresponds
  to blueprint label `thm:physics:phyx_mini_0093:target`.

The target environment is ready for a `\lean{...}` reference and `\leanok`.
The blueprint was not edited because the explicit prover permissions make it
read-only and the project guide assigns `\leanok` bookkeeping to the sync
phase. The supporting public declarations above currently have no individual
blueprint labels; a blueprint-writing lane should add them if declaration-level
coverage is desired.

## LeanExplore queries and candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- Natural language: `Malus law polarized light intensity cosine squared ideal
  linear polarizer`. No optics law was found. `Real.cos_sq` was the sole
  physically adjacent hit, but it is an algebraic identity rather than
  Malus's law, so it was not substituted for the missing governing law.
- Natural language: `polarization state unpolarized linearly polarized light`.
  Hits concerned algebraic polarization identities, not optical polarization
  states; none was suitable.
- Natural language: `optical intensity physical dimension polarization
  electromagnetic wave` and `physical dimension intensity power per area`.
  These recovered Physlib's `Dimension`, `WithDim`, `Dimension.M𝓭`,
  `Dimension.T𝓭`, `DimEnergy`, and `DimArea`; the first four were selected to
  express the intensity dimension directly as `M/T³`.
- Likely names: `Dimension.M𝓭`, `Dimension.T𝓭`, `WithDim physical quantity
  real scalar units`, and `WithDim.val_zero`. These grounded the selected
  dimension tag, scalar projection, order/zero behavior, and dimensioned zero.
- Likely names: `Real.cos`, `Real.pi`, and `Real.cos_pi_div_two`. These
  grounded the radian angle constants and the cosine appearing in the local
  Malus-law relation. `Real.cos_pi_div_two_sub` is proof-relevant but is not
  used to hide the result in the statement.

Source, module, and docstring were fetched for the candidates used in the
formalization:

- `Dimension` (id 394292), `Dimension.M𝓭` (id 394336), and
  `Dimension.T𝓭` (id 394330), module `Physlib.Units.Dimension`;
- `WithDim` (id 394425), `WithDim.instZero` (id 394431), and
  `WithDim.val_zero` (id 394432), module
  `Physlib.Units.WithDim.Basic`;
- `Real.cos` (id 128820), module
  `Mathlib.Analysis.Complex.Trigonometric`;
- `Real.pi` (id 146728), module
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.M𝓭`, `Dimension.T𝓭`, `WithDim`,
  `WithDim.val`, the inherited order on `WithDim`, and dimensioned zero.
- Mathlib: `Real.cos`, `Real.pi`, real arithmetic, order, powers, and exact
  rational divisions for the radian angle readouts.

## Local abstractions introduced

- `PolarizationState` distinguishes unpolarized light from linear
  polarization with a radian axis. A local type is needed because searches
  found no library optical polarization-state type that includes unpolarized
  beams.
- `LightBeam` couples a dimensioned optical intensity to its polarization.
- `IdealLinearPolarizer` preserves the physical filter role and axis rather
  than representing a filter by a bare angle.
- `PassesThroughIdealLinearPolarizer` is a faithful local governing-law
  predicate because no Mathlib/Physlib Malus-law API was found.
- The setup/readout/law structures separate physical objects, primary-image
  evidence, and governing-law applications from the current conclusion.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration for ideal linear polarizers, unpolarized
  attenuation, or Malus's law was found. The local abstractions should remain
  unless that API is added.
- `Physlib.Optics.Polarization.Basic` exists in the installed source tree but
  currently contains only module documentation and no reusable optical
  polarization declarations.
- The requested current `.archon/AGENTS.md` is absent. The prover role was
  recovered from the matching archived project guide; its restrictions agree
  with the invocation. There were no `/- USER: ... -/` comments in the
  assigned file.
- The requested `archon dag-query` could not run because `archon` is not on
  `PATH` in this environment (`exit 127`). The source report independently
  confirms there are no previous parts.

## Autoformalization verification (before prover iteration 008)

- Lean LSP diagnostics report no errors or failed dependencies and exactly
  one expected `sorry` warning for the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0093.lean` exited 0 with
  exactly that same single warning.

# Prover result: iteration 008

## `intensity_at_C_after_removing_middle_filter` (line 134)

### Attempt 1

- **Approach:** Apply `WithDim.ext`, obtain the linear polarization of the
  beam after A from `through_A`, substitute it into the direct A-to-C
  transition `without_B_through_C`, then rewrite the pictured axes as `0` and
  `Real.pi / 2`.
- **Result:** RESOLVED.
- **Key insight:** After those substitutions, `simp` uses
  `Real.cos_pi_div_two` to reduce the Malus-law factor
  `cos (π / 2 - 0) ^ 2` to zero. The scalar equality then proves equality of
  the dimension-tagged intensities by `WithDim.ext`.

## Verification after proof

- Lean LSP diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0093.lean`: exited 0 with
  no output.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Theorem axiom verification reports only the standard foundational axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- No declarations or helper lemmas were added.
- The blueprint chapter was not edited because this prover lane grants write
  permission only to the assigned Lean file and this task-result file;
  `\leanok` bookkeeping remains for the authorized sync phase.

## Redraft needed

None.

## Summary

- Sorry count: 1 → 0.
- Closed:
  `PhyXMiniProblems.ProblemPhyXMini0093.intensity_at_C_after_removing_middle_filter`.
- Still open: none.
- Adjacent sorries attempted: not applicable; this was the only `sorry` in
  the assigned file.

## Why I stopped

Real progress: closed the sole assigned `sorry` with a compiling proof. The
assigned file has no remaining proof obligations.

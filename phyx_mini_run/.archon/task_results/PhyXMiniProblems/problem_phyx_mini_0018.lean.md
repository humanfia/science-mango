# Autoformalization result: `problem_phyx_mini_0018.lean`

The assigned Lean file already contained a complete, dimension-aware draft.
Iteration 003 rechecked it against the exact final-review gate reason, source
report, primary image, blueprint, Mathlib, and Physlib. Its declarations remain
faithful and compile, so no statement churn was needed. No
`/- USER: ... -/` hint occurs in the file.

The exact retry reason was missing post-formalization evidence. This report is
the regenerated evidence based on the declarations actually present and the
searches actually run during this audit.

## Assumption/target split

### Governing laws

- `SatisfiesSnellLawAt setup .curvedEntry` states
  `n_vacuum * sin α = n_material * sin β` at the radial entry normal.
- `SatisfiesSnellLawAt setup .flatExit` states
  `n_material * sin δ = n_vacuum * sin θ` at the horizontal normal to the
  vertical exit face.
- `ObeysQuarterCircleGeometry` includes straight-ray/quarter-circle geometry:
  the incoming direction is horizontal and the internal downward angle is
  `δ = α - β`.

### Previous-part results

- None. The source report has `previous_parts: []`.
- Consequently, `β = arcsin (L / (nR))` is the conclusion of
  `curvedRefractionAngle_eq_arcsin`, not an assumed previous-part fact.

### Figure/data readouts

- `QuarterCircleRefractionSetup.radius` is the dimensionful radius `R`, and
  `incomingHeightAboveBase` is the dimensionful height `L`.
- The primary image shows a quarter disk with a horizontal base, a vertical
  exit face, a horizontal incoming ray at height `L`, the radial curved-face
  normal, and the outgoing angle `θ` below the horizontal exit normal.
- The radial geometry gives `α = arcsin (L / R)`; this is recorded in
  `ObeysQuarterCircleGeometry` after explicit SI scalar readout.
- `HasPhysicalParameters` records vacuum index one, an optically denser
  material, and `0 < L < R`.
- `HasPhysicalRayAngles` selects the acute physical branches for `α`, `β`,
  `δ`, and `θ`; in particular, it models the pictured transmitted exit ray
  rather than total internal reflection.

### Current target conclusions

- `curvedRefractionAngle_eq_arcsin` concludes the derived entry result
  `β = arcsin (L / (nR))`.
- `problem_phyx_mini_0018` concludes
  `θ = arcsin (n * sin (arcsin (L / R) - arcsin (L / (nR))))`, exactly the
  physically supported recorded answer C.

## Goal-faithfulness audit

- The final closed form for `θ` occurs only in the conclusion of
  `problem_phyx_mini_0018` (besides documentation).
- `HasPhysicalParameters` contains only medium/index and nondegenerate-length
  conditions. `HasPhysicalRayAngles` contains only inverse-trigonometric branch
  conditions; neither determines `θ` numerically or by the requested formula.
- `ObeysQuarterCircleGeometry` determines `α` and relates `δ`, `α`, and `β`,
  but contains no emergence-angle equation.
- The flat-exit branch of `SatisfiesSnellLawAt` mentions `θ` only through the
  target-independent governing law `n₁ sin θ₁ = n₂ sin θ₂`; it does not unfold
  to the requested answer.
- The intermediate `β` formula remains a lemma conclusion and is not present
  in a premise structure or theorem hypothesis.
- No `Laws`, `Valid...Physics`, `Satisfies...`, helper definition, or local
  definition contains the current closed-form target, and no target is true by
  reflexivity or definition unfolding.

## Declarations and blueprint correspondence

- `DimLength` — Physlib dimensionful length type; blueprint label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-dimlength`.
- `lengthInMeters` — explicit SI scalar projection used to form dimensionless
  trigonometric ratios; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-lengthinmeters`.
- `OpticalMedium` — a homogeneous optical medium with a positive,
  dimensionless refractive-index readout; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-opticalmedium`.
- `OpticalInterface` — distinct curved-entry and flat-exit surfaces; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-opticalinterface`.
- `QuarterCircleRefractionSetup` — media, figure labels `R` and `L`, and the
  distinct incident, refracted, internal, and emergence angle readouts; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-quartercirclerefractionsetup`.
- `HasPhysicalParameters` — target-independent medium and nondegeneracy facts;
  label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-hasphysicalparameters`.
- `HasPhysicalRayAngles` — target-independent acute-branch facts; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-hasphysicalrayangles`.
- `ObeysQuarterCircleGeometry` — target-independent figure geometry; label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-obeysquartercirclegeometry`.
- `SatisfiesSnellLawAt` — target-independent governing law at each interface;
  label
  `def:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-satisfiessnelllawat`.
- `curvedRefractionAngle_eq_arcsin` — derived entry-face supporting lemma;
  label
  `lem:physics:phyx-mini-0018:phyxminiproblems-problemphyxmini0018-curvedrefractionangle-eq-arcsin`.
- `problem_phyx_mini_0018` — the final emergence-angle relation; label
  `thm:physics:phyx_mini_0018:target`.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `Snell's law refraction refractive index incident
  angle transmitted angle geometrical optics`: returned vector/triangle-angle
  and Euclidean law-of-sines declarations, including
  `InnerProductGeometry.sin_angle_div_norm_eq_sin_angle_div_norm` and
  `EuclideanGeometry.sin_angle_div_dist_eq_sin_angle_div_dist`. These are not
  laws of optical refraction and were not used.
- Likely-name query `SnellLaw refraction optics`: again returned Euclidean law
  of sines and unrelated polynomial-law declarations; no Snell API was found.
- Query `Real.arcsin inverse sine real`: selected `Real.arcsin` and `Real.sin`.
  Their source and modules were fetched: respectively
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` and
  `Mathlib.Analysis.Complex.Trigonometric`.
- Query `Dimensionful physical length quantity SI units WithDim`: selected
  `Dimensionful` and `UnitChoices.SI`; their sources/modules were fetched from
  `Physlib.Units.Basic`.
- Likely-name queries `WithDim dimension wrapper` and
  `Dimension.L𝓭 length dimension` grounded the dimension-tagging API and
  `Dimension.L𝓭`. The source/module for `Dimension.L𝓭` was fetched from
  `Physlib.Units.Dimension`; LSP local search and hover confirmed the exact
  `WithDim (d : Dimension) (M : Type)` declaration in
  `Physlib.Units.WithDim.Basic`.
- LSP local search for `Snell` returned no declaration.

## Physlib/Mathlib names grounded

- Mathlib: `Real.sin`, `Real.arcsin`, `Real.pi`, `Set.Ioo`, and `NNReal`.
- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI`.

## Local abstractions introduced

- `DimLength` abbreviates the genuine Physlib type
  `Dimensionful (WithDim Dimension.L𝓭 NNReal)`; it is not a scalar alias.
- `lengthInMeters` is explicitly a scalar measurement projection. Only its
  dimensionless length ratios are passed to `sin`/`arcsin`.
- `OpticalMedium`, `OpticalInterface`, and
  `QuarterCircleRefractionSetup` preserve distinct media, surfaces, physical
  lengths, and normal-relative angle roles absent from the available library.
- `SatisfiesSnellLawAt` is the smallest faithful replacement for the missing
  optics API. It states Snell's governing equation separately at each physical
  interface and does not encode the requested closed form.

## Source/law/answer audit

- The source statement and primary image say/show a quarter circle. The
  auxiliary generated caption says “semi-circular”; the formalization follows
  the primary evidence and source statement.
- The image labels `θ` outside the vertical exit face against a dashed
  horizontal line, so modeling it from the horizontal face normal is correct.
- Applying the radial entry geometry and Snell's law at both faces yields
  choice C, matching the recorded answer. No answer discrepancy needs to be
  retained as metadata.

## Grounding gaps and redraft requests

- Mathlib/Physlib provides no geometrical-optics ray model or Snell-law
  declaration found by either semantic, likely-name, or local search; the local
  physical interfaces above fill this gap.
- `.archon/AGENTS.md` is absent in this checkout. The current
  `.archon/prover-modes/physics-formalize.md`, `PROGRESS.md`, supplied role
  instructions, and iteration-003 plan/objectives were consulted instead.
- Although the prompt says `archon` is on `PATH`, `command -v archon` and the
  requested DAG query fail with `command not found`. The target's exact local
  `\uses{}` pins were therefore inspected directly in the chapter; no
  dependency name was guessed.
- No blueprint redraft is requested. The chapter has `% archon:physics`, the
  correct source/image/answer material, and the target environment. That
  environment is ready for the loop-managed `\leanok`; it was not edited
  because prover write permissions explicitly exclude blueprint chapters.

## Verification

- `archon-lean-lsp` reports exactly two expected `declaration uses sorry`
  warnings, for `curvedRefractionAngle_eq_arcsin` and
  `problem_phyx_mini_0018`, with no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0018.lean` exits with code
  zero and the same two warnings.

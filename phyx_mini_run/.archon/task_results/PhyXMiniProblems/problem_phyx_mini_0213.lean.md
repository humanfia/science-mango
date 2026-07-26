# Autoformalization result: `problem_phyx_mini_0213.lean`

Iteration 003 performed a fresh post-formalization audit. The exact review-gate
reason was missing evidence, not a semantic defect. The existing Lean model was
therefore preserved after rechecking the source report, primary bitmap,
blueprint, Mathlib/Physlib grounding, and elaborated declaration signatures.

## Assumption/target split

### Governing laws

- `SatisfiesTreeBranchResonanceLaws.waveSpeedEqualsFrequencyTimesWavelength`
  states the nondispersive branch-wave law `v = f_branch * λ` in every coherent
  `UnitChoices` readout.
- `SatisfiesTreeBranchResonanceLaws.soundFrequencyEqualsBranchFrequency`
  states that the radiated tone has the same ordinary frequency as the
  vibrating branch.
- `HasPhysicalTreeBranchParameters` states that the span, wavelength, wave
  speed, branch frequency, and radiated frequency are positive. In particular,
  the positive SI span licenses division by `4 L` in the main target.

### Previous-part results

- None. `reports/phyx_mini/problem_phyx_mini_0213.source.json` has an empty
  `previous_parts` array.

### Figure/data readouts

- The primary raster `phyx_data/test_image/213.png` was inspected directly. It
  labels the trunk attachment as a node, the branch end near the bird as an
  antinode, and their separation as `1/4 λ`.
- `MatchesSuppliedTreeBranchFigure` records the transverse standing-wave kind,
  the node and antinode roles, the bird-side endpoint, positions measured from
  the trunk, and `4 * span = wavelength` in every coherent unit system.
- `MatchesProblemScenario` records wind as the excitation source.
- Neither the image nor the prose supplies a numerical span, wavelength,
  branch-wave speed, or frequency.
- `displayedAnswerFrequencyHertz` transcribes A `440 Hz`, B `460 Hz`, C
  `480 Hz`, and D `500 Hz`; `recordedDatasetAnswer` transcribes the dataset's D
  label. These declarations are source metadata and are not physical premises.

### Current target conclusions

- `quarterWave_branchFrequency_relation` concludes the readout-independent
  cross-multiplied relation `4 L f_branch = v`.
- `quarterWave_soundFrequency_relation` concludes `4 L f_sound = v`.
- `problem_phyx_mini_0213` concludes the SI formula
  `f_sound = v / (4 L)`. This is the strongest frequency conclusion supported
  by the supplied figure and governing laws; it does not assert the unsupported
  numerical value `500 Hz`.

## Goal-faithfulness audit

`TreeBranchResonanceSetup` stores span, standing wavelength, branch-wave speed,
branch frequency, and radiated frequency as independent dimensionful fields.
No field assigns a numerical answer or defines one physical field from another.

The derivation remains split across genuinely prior inputs:
`MatchesSuppliedTreeBranchFigure` gives `λ = 4 L`, while
`SatisfiesTreeBranchResonanceLaws` separately gives
`v = f_branch * λ` and `f_sound = f_branch`. The main target
`f_sound = v / (4 L)` occurs in no hypothesis, premise structure, governing-law
field, or local definition. Deriving it still requires both physical laws, the
figure relation, and positivity of the span.

The value `500` appears only in the displayed-answer table. Neither
`AgreesWithDisplayedFrequencyChoice setup recordedDatasetAnswer` nor any
`500 Hz` equality is assumed. Thus the recorded D answer has not been smuggled
into the model, and an underdetermined numeric conclusion is not claimed.

## Declarations and blueprint correspondence

All names below are in namespace
`PhyXMiniProblems.ProblemPhyXMini0213`.

| Lean declaration | Blueprint label |
| --- | --- |
| `LengthQuantity` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-lengthquantity` |
| `FrequencyQuantity` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-frequencyquantity` |
| `BranchWaveSpeed` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-branchwavespeed` |
| `lengthReadout` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-lengthreadout` |
| `frequencyReadout` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-frequencyreadout` |
| `speedReadout` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-speedreadout` |
| `lengthInMeters` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-lengthinmeters` |
| `frequencyInHertz` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-frequencyinhertz` |
| `speedInMetersPerSecond` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-speedinmeterspersecond` |
| `BranchFigurePoint` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-branchfigurepoint` |
| `StandingWaveRole` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-standingwaverole` |
| `BranchWaveKind` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-branchwavekind` |
| `BranchExcitationSource` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-branchexcitationsource` |
| `TreeBranchFigure` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-treebranchfigure` |
| `TreeBranchResonanceSetup` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-treebranchresonancesetup` |
| `MatchesProblemScenario` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-matchesproblemscenario` |
| `MatchesSuppliedTreeBranchFigure` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-matchessuppliedtreebranchfigure` |
| `HasPhysicalTreeBranchParameters` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-hasphysicaltreebranchparameters` |
| `SatisfiesTreeBranchResonanceLaws` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-satisfiestreebranchresonancelaws` |
| `quarterWave_branchFrequency_relation` | `lem:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-quarterwave-branchfrequency-relation` |
| `quarterWave_soundFrequency_relation` | `lem:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-quarterwave-soundfrequency-relation` |
| `AnswerChoice` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-answerchoice` |
| `displayedAnswerFrequencyHertz` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-displayedanswerfrequencyhertz` |
| `recordedDatasetAnswer` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-recordeddatasetanswer` |
| `AgreesWithDisplayedFrequencyChoice` | `def:physics:phyx-mini-0213:phyxminiproblems-problemphyxmini0213-agreeswithdisplayedfrequencychoice` |
| `problem_phyx_mini_0213` | `thm:physics:phyx_mini_0213:target` |

The chapter already contains the corresponding `\lean{...}` pins. It contains
no `\leanok` markers. This agent did not add them because the task's explicit
write permissions prohibit editing blueprint chapters; a blueprint-authorized
coordinator should mark these environments after accepting the formalization.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- `dimensionful physical quantities length frequency speed unit choices`
  returned `Dimensionful`, `UnitChoices.SI`, `UnitChoices`, and `DimSpeed`-related
  declarations.
- `DimSpeed Dimensionful WithDim UnitChoices` returned `Dimensionful`,
  `DimSpeed`, `instCoeFunDimensionfulForallUnitChoices`, and unit-scaling API.
- `physical frequency inverse time dimension Dimensionful` returned
  `Dimensionful`, `Dimension`, and `Dimension.inv_time`.
- `WithDim physical dimensions typed quantity` and the exact-name query
  `WithDim` returned `WithDim`, `WithDim.le_def`, and related tagged-value API.
- `Dimension.L𝓭 Dimension.T𝓭` returned the length- and time-dimension constants.
- `standing wave node antinode wavelength frequency` and
  `wave speed equals frequency times wavelength sound wave` returned
  `ClassicalMechanics.WaveEquation`, `ClassicalMechanics.harmonicWave`,
  `ClassicalMechanics.planeWave`, and
  `ClassicalMechanics.transverseHarmonicPlaneWave`. These are general or
  plane-wave objects, not a model of a finite branch with labeled node and
  antinode boundary geometry.

Source, module, and docstring data were fetched for the dimensional candidates
used by the file:

- `Dimensionful` (id 394284), `UnitChoices` (id 394255), and
  `UnitChoices.SI` (id 394270), from `Physlib.Units.Basic`;
- `Dimension` (id 394292), `Dimension.L𝓭` (id 394324), and
  `Dimension.T𝓭` (id 394330), from `Physlib.Units.Dimension`;
- `WithDim` (id 394425) and `WithDim.le_def` (id 394446), from
  `Physlib.Units.WithDim.Basic`;
- `DimSpeed` (id 394481), from `Physlib.Units.WithDim.Speed`, whose source is
  `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)`.

The Lean LSP independently confirmed the imported types and documentation for
`Dimensionful`, `WithDim`, `DimSpeed`, and `UnitChoices.SI` in the assigned
file.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `UnitChoices`, `UnitChoices.SI`, and `DimSpeed`.
- Mathlib: `NNReal`/`ℝ≥0` for nonnegative physical magnitudes, `ℝ` for
  explicitly named scalar readouts and displayed answer values, real
  multiplication/division, and ordinary inductive datatypes.

## Local abstractions introduced

- `LengthQuantity` and `FrequencyQuantity` specialize Physlib's
  unit-independent `Dimensionful (WithDim _ NNReal)` representation to length
  and inverse-time dimensions. They preserve physical roles and are not scalar
  aliases.
- The four small inductive label types distinguish figure points,
  displacement roles, wave kind, and excitation source.
- `TreeBranchFigure` and `TreeBranchResonanceSetup` preserve the geometry and
  keep wavelength, wave speed, branch frequency, and sound frequency
  independent.
- `MatchesSuppliedTreeBranchFigure` is the smallest local interface for the
  bitmap's node/antinode and quarter-wave evidence.
- `SatisfiesTreeBranchResonanceLaws` is a local governing-law interface because
  the searched libraries provide no compatible finite standing-wave resonance
  object. It states generic source laws, not the theorem's divided target or a
  numeric answer.

## Grounding gaps and redraft requests

- No searched Mathlib/Physlib declaration directly models a finite transverse
  standing wave with labeled node and antinode endpoints and a quarter-wave
  span. The general and plane-wave declarations are near misses, so the local
  interfaces above are retained.
- The supplied source cannot determine `500 Hz`: it gives neither a numerical
  `L` nor a numerical `v`. If an authoritative version intends choice D as a
  physical consequence, it must add an independent length and branch-wave-speed
  calibration (or equivalent prior experimental data). Until then, the symbolic
  formula is the strongest supported target and D remains metadata only.
- The requested `.archon/AGENTS.md` does not exist. The available active role
  file `.archon/prover-modes/physics-formalize.md` was read and followed.
- The advertised `archon` executable is not on `PATH`, so the optional DAG
  query could not be run. The source report independently establishes that
  there are no previous parts.
- No `/- USER: ... -/` hint occurs in the assigned Lean file.

## Verification

- `archon-lean-lsp` elaborated the file with exactly three expected
  `declaration uses sorry` warnings (the two lemmas and main theorem), no
  errors, and no failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0213.lean` exited 0 with
  the same three expected warnings and no errors.

# Prover result — iteration 019

## Outcome

All three assigned placeholders were closed without changing any declaration
header, hypothesis, or conclusion.

- `queryElapsedTime_from_speed` uses the positive queried velocity to rewrite
  its magnitude, obtains the signed velocity readout `25`, and solves
  `25 = 15 + 4 Δt` for `Δt = 5 / 2`.
- `queriedPosition_from_kinematics` substitutes that elapsed time and the
  stated SI readouts into the position-evolution law to derive `55`.
- `problem_phyx_mini_0793` applies the position lemma and checks the four
  displayed choices by cases, proving that recorded choice B is the unique
  match.

No redraft is needed.

## Verification

- `archon-lean-lsp` reports no diagnostics.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0793.lean` exits with
  status 0 and no output.
- The assigned file contains no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, or other escape hatch.
- The theorem verification scan reports no warnings. Its only axiom
  dependencies are Lean/Mathlib's standard `propext`, `Classical.choice`, and
  `Quot.sound`.
- `git diff --check` and the over-100-character line scan report no issues.

## Blueprint status

The theorem and both lemma environments are ready for `\leanok`. I did not
edit the blueprint chapter because the task's explicit write-permission rule
permits edits only to the assigned Lean file and this result file and expressly
forbids editing the blueprint chapter.

---

# Post-formalization report — iteration 003

## Review outcome

The formalization-gate reason was missing genuine post-formalization evidence,
not a stated semantic defect. I re-audited the existing Lean declaration
against the blueprint, source JSON, and primary bitmap, reran LeanExplore
grounding, and recompiled the assigned file. The physical statement is
faithful, so the Lean file was deliberately preserved without a semantic
redraft.

## Assumption/target split

### Governing laws

- `SatisfiesConstantAccelerationKinematics.velocityEvolution` is the general
  signed one-dimensional law `v(t) = v(t₀) + a (t - t₀)` in every coherent
  choice of units.
- `SatisfiesConstantAccelerationKinematics.positionEvolution` is the general
  position law `x(t) = x(t₀) + v(t₀)(t-t₀) + (1/2)a(t-t₀)^2` in every
  coherent choice of units.
- `SatisfiesConstantAccelerationKinematics.speedIsVelocityMagnitude` relates
  the independent nonnegative speed observable to the magnitude of the signed
  east-west velocity component.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Problem and figure/data readouts

- `MatchesProblemStatement` records the city-limits signpost at the coordinate
  origin, `t₀ = 0 s`, `x₀ = 5 m`, `v₀x = 15 m/s`, constant
  `aₓ = 4 m/s²`, and the condition selecting the requested event,
  `speed(queryTime) = 25 m/s`.
- `MatchesSuppliedMotorcycleFigure` records the two motorcycles, the `OSAGE`
  sign, the origin `O`, the east-positive `x` axis, all displayed symbolic
  labels and arrows, and the separate unknown later snapshot at `t = 2.0 s`.
  Its unknown position and velocity are tied to the physical trajectory but
  are not assigned scalar values.
- `HasPhysicalEastwardQueryEvent` records only the future-time branch and the
  eastward signs of the initial velocity, queried velocity, and acceleration.

### Current target conclusions

- `queryElapsedTime_from_speed`: the requested event is `5/2 s` after the
  initial event.
- `queriedPosition_from_kinematics`: the requested position is `55 m` east of
  the signpost.
- `problem_phyx_mini_0793`: that position is `55 m`, recorded choice B agrees
  with it, and B is the unique matching displayed choice.

## Goal-faithfulness audit

The value `55` and answer label B do not occur in `MatchesProblemStatement`,
`MatchesSuppliedMotorcycleFigure`, `HasPhysicalEastwardQueryEvent`, or
`SatisfiesConstantAccelerationKinematics`. The setup's `queryTime`, trajectory
position, velocity, and speed are independent fields; none is defined from a
recorded answer. The `25 m/s` equation is an input event condition from the
question, not the requested position. The `t = 2.0 s` figure snapshot is kept
as a distinct figure time and is deliberately not equated with `queryTime`.

`displayedPositionMeters .B = 55` is only the literal answer-list readout. The
substantive physical equality
`queriedPositionEastOfSignpostMeters setup = 55` remains a theorem/lemma
conclusion requiring the kinematic premises; it cannot be obtained by
unfolding the trajectory or setup.

## Source/law/answer audit

- Source: the source JSON and primary bitmap `793.png` agree on an
  east-positive road axis with the OSAGE signpost at the origin, the initial
  readouts `x₀ = 5.0 m`, `t₀ = 0 s`, `v₀x = 15 m/s`, and the eastward
  acceleration `aₓ = 4.0 m/s²`. The bitmap also shows a distinct snapshot at
  `t = 2.0 s` whose `x` and `vₓ` readouts are question marks.
- Laws: the formal premises use the general constant-acceleration velocity and
  position laws plus speed as the magnitude of signed velocity. They do not
  encode the requested elapsed time, position, or answer label.
- Answer: on the eastward branch, `25 = 15 + 4 Δt` gives `Δt = 5/2 s`, and
  `5 + 15(5/2) + (1/2)4(5/2)^2 = 55 m`. Thus the recorded answer B is
  physically consistent and is the unique displayed choice with value `55`.
- Separation: the figure's `2.0 s` snapshot is retained as evidence but is not
  identified with the `25 m/s` query event; at `2.0 s` the stated laws would
  give only `23 m/s`.

## Declarations created and blueprint correspondence

For compactness, let
`D = def:physics:phyx-mini-0793:phyxminiproblems-problemphyxmini0793-` and
`L = lem:physics:phyx-mini-0793:phyxminiproblems-problemphyxmini0793-`.
The declaration topology gives these exact correspondences:

- Dimensionful roles (under prefix `D`): `SignedPositionQuantity` ↔ suffix
  `signedpositionquantity`, `TimeQuantity` ↔ `timequantity`,
  `SignedVelocityQuantity` ↔ `signedvelocityquantity`, `SpeedQuantity` ↔
  `speedquantity`, and `SignedAccelerationQuantity` ↔
  `signedaccelerationquantity`.
- Coherent readouts (under `D`): `positionReadout` ↔ `positionreadout`,
  `timeReadout` ↔ `timereadout`, `velocityReadout` ↔ `velocityreadout`,
  `speedReadout` ↔ `speedreadout`, and `accelerationReadout` ↔
  `accelerationreadout`.
- SI projections (under `D`): `positionInMeters` ↔ `positioninmeters`,
  `timeInSeconds` ↔ `timeinseconds`, `velocityInMetersPerSecond` ↔
  `velocityinmeterspersecond`, `speedInMetersPerSecond` ↔
  `speedinmeterspersecond`, and `accelerationInMetersPerSecondSquared` ↔
  `accelerationinmeterspersecondsquared`.
- Figure vocabulary and setup (under `D`): `CardinalDirection` ↔
  `cardinaldirection`, `FigureObject` ↔ `figureobject`, `FigureLabel` ↔
  `figurelabel`, `SuppliedMotorcycleFigure` ↔ `suppliedmotorcyclefigure`, and
  `MotorcycleMotionSetup` ↔ `motorcyclemotionsetup`.
- Premise interfaces: `MatchesProblemStatement` ↔
  suffix `matchesproblemstatement`, `MatchesSuppliedMotorcycleFigure` ↔
  `matchessuppliedmotorcyclefigure`, `HasPhysicalEastwardQueryEvent` ↔
  `hasphysicaleastwardqueryevent`, and
  `SatisfiesConstantAccelerationKinematics` ↔
  `satisfiesconstantaccelerationkinematics`, all under `D`.
- Derived quantities and results: `queryElapsedTimeSeconds` ↔
  suffix `queryelapsedtimeseconds` under `D`,
  `queriedPositionEastOfSignpostMeters` ↔ `queriedpositioneastofsignpostmeters`
  under `D`, `queryElapsedTime_from_speed` ↔
  `queryelapsedtime-from-speed` under `L`, and
  `queriedPosition_from_kinematics` ↔ `queriedposition-from-kinematics` under
  `L`.
- Displayed-answer layer (under `D`): `AnswerChoice` ↔ `answerchoice`,
  `displayedPositionMeters` ↔ `displayedpositionmeters`,
  `recordedAnswerChoice` ↔ `recordedanswerchoice`,
  `MatchesDisplayedPosition` ↔ `matchesdisplayedposition`, and
  `IsUniqueMatchingDisplayedChoice` ↔
  `isuniquematchingdisplayedchoice`.
- Main declaration `problem_phyx_mini_0793` ↔
  `thm:physics:phyx_mini_0793:target`.

The blueprint environment was not edited to add `\leanok`, because the task's
explicit write-permission section permits edits only to the assigned Lean file
and this task-result file and expressly forbids editing blueprint chapters.

## LeanExplore queries and candidates

The following are the searches actually rerun for this iteration. Every search
used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `one dimensional constant acceleration kinematics
  velocity position` returned `RigidBodyMotion.velocity`,
  `ClassicalMechanics.FreeParticle.velocity`, and
  `ClassicalMechanics.FreeParticle.velocity_const_of_zero_acc` among the
  leading candidates. These do not provide the required accelerating
  one-dimensional trajectory model.
- Likely-name query `ConstantAcceleration` returned
  `HasConstantSpeedOnWith`, Navier--Stokes material acceleration, and harmonic
  oscillator declarations, but no suitable constant-acceleration kinematics
  interface.
- Combined concept/name query `Dimensionful WithDim UnitChoices SI coherent
  physical units` found `Dimensionful`, `UnitChoices.SI`, and the coherent-unit
  scaling infrastructure.
- Likely-name query `WithDim` found the exact dimension-tagged carrier used in
  the file. Query `Dimension L𝓭 T𝓭` found `Dimension.L𝓭` and `Dimension.T𝓭`,
  and query `UnitChoices.SI` found the exact SI unit-system declaration.
- Natural-language query `NNReal nonnegative real number` found `NNReal` and
  its real coercion API, grounding the nonnegative speed carrier.
- Likely-name queries `WithDim`, `UnitChoices.SI`, and `Dimensionful` confirmed
  the exact declarations selected by the file.
- Query `DimLength DimTime DimSpeed DimAcceleration` returned `DimSpeed` but no
  complete family providing the distinct signed position, physical time,
  signed velocity, nonnegative speed magnitude, and signed acceleration roles
  required here. The selected `Dimensionful (WithDim d M)` representation
  expresses all five roles uniformly and preserves the deliberate distinction
  between signed velocity (`ℝ`) and speed magnitude (`NNReal`).

Source, module, and docstring details were fetched for every selected
candidate actually used: `Dimensionful` (ID 394284,
`Physlib.Units.Basic`), `WithDim` (ID 394425,
`Physlib.Units.WithDim.Basic`), `UnitChoices.SI` (ID 394270,
`Physlib.Units.Basic`), `Dimension.L𝓭` (ID 394324,
`Physlib.Units.Dimension`), `Dimension.T𝓭` (ID 394330, same module), and
`NNReal` (ID 211536, `Mathlib.Data.NNReal.Defs`).

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.T𝓭`, and
  `UnitChoices.SI`.
- Mathlib/core numeric infrastructure: `ℝ`, `NNReal`, absolute value, powers,
  finite inductive types, strings, and booleans.

## Local abstractions introduced

- The five quantity abbreviations specialize Physlib's unit-independent
  `Dimensionful (WithDim d M)` representation. They are dimension-tagged
  physical quantities, not scalar aliases or one-field scalar wrappers.
- `MotorcycleMotionSetup` keeps the trajectory and selected event independent
  of the answer.
- `SatisfiesConstantAccelerationKinematics` was introduced because the search
  found no matching general one-dimensional constant-acceleration API. It
  states the standard laws directly in arbitrary coherent unit choices.
- The figure structures preserve the literal geometry, directions, labels,
  and the physically separate `2.0 s` snapshot from the primary bitmap.

## Grounding gaps and redraft requests

- No library declaration matching the required general one-dimensional
  constant-acceleration model was found; the faithful local law interface is
  therefore necessary.
- The blueprint chapter exists and is marked `% archon:physics`, but its proof
  paragraph contains only generic autoformalization instructions rather than
  the informal calculation. A future plan-agent redraft could explicitly add
  `25 = 15 + 4 t`, hence `t = 2.5 s`, followed by
  `x = 5 + 15(2.5) + (1/2)4(2.5)^2 = 55 m`.
- The requested `.archon/AGENTS.md` was absent in this workspace. The available
  `.archon/prover-modes/physics-formalize.md` and the full task instructions
  were used as the role specification.
- The `archon` executable advertised for DAG queries was not available on the
  shell `PATH`; no dependency declarations were needed for this standalone
  formalization.

## Verification

- In iteration 003, `archon-lean-lsp` diagnostics reported success with
  exactly three expected `declaration uses sorry` warnings and no errors or
  failed dependencies.
- The iteration-003 command
  `lake env lean PhyXMiniProblems/problem_phyx_mini_0793.lean` exited with
  status 0 and emitted the same three expected `sorry` warnings.
- A trailing-whitespace scan reported no issues in either permitted output
  file.

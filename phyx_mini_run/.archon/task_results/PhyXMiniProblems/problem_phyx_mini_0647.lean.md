# Autoformalization result: `problem_phyx_mini_0647.lean`

## Iteration 003 retry resolution

The formalization gate's exact retry reason was missing post-formalization
evidence, not a defect in the revised Lean statement. I re-read the `%
archon:physics` blueprint chapter, the assigned Lean file and its `USER` hint,
the source report, and the primary raster `647.png`, and then re-ran the
LeanExplore searches listed below against the declarations actually present.

The audit found no source, law, or answer-separation defect. In accordance with
the final-retry protocol, the existing declaration names, signatures, and
topology were preserved. No Lean source redraft was needed in iteration 003.

## Assumption/target split

- Governing laws:
  - `QuantumMechanics.OneDimension.HilbertSpace.MemHS` requires the complex
    coordinate wavefunction to be square-integrable with respect to Lebesgue
    volume;
  - `SatisfiesBornPositionPhysics.probabilityMeasureHasBornDensity` imposes the
    position-space Born rule by identifying the independent probability measure
    with Lebesgue volume having density
    `ENNReal.ofReal (Complex.normSq (ψ x))`;
  - `MeasureTheory.ProbabilityMeasure` supplies normalization (total mass one).
- Previous-part results: none. The source report's `previous_parts` array is
  empty.
- Figure/data readouts:
  - the particle is an electron;
  - the horizontal axis is position in nanometres and the vertical axis is
    `ψ(x)`;
  - the displayed position ticks are `-2`, `-1`, `1`, and `2` nm;
  - the displayed amplitude ticks are `-c`, `-c/2`, `c/2`, and `c`, with the
    amplitude scale `c` positive and interpreted as an inverse-square-root-
    nanometre scalar readout;
  - the primary raster shows zero amplitude outside `[-2, 2]`, amplitude
    `-c/2` on each outer plateau, and amplitude `c` on the central plateau.
    The auxiliary prose's claim that the outer plateaus equal `-c` contradicts
    the raster and is therefore not used.
- Current target conclusions:
  - the dimensionless Born probability on the closed interval from `-1 nm` to
    `1 nm` is exactly `4/5 = 0.80`;
  - answer choice B is the displayed choice matching this probability.

## Source/law/answer audit

The source contributes only the scenario, raster readouts, question interval,
and answer-choice metadata. The general Born density relation and Hilbert-space
membership are isolated in `SatisfiesBornPositionPhysics`. The electron and
image facts are isolated in `MatchesProblemStatementAndFigure`. The requested
probability and matching answer occur only in the conclusions of
`central_interval_probability` and `problem_phyx_mini_0647` (or in the generic
answer-comparison definition described below).

The raster's outer levels at `-c/2` are mathematically consistent with the
recorded answer: the two outer unit-width intervals contribute a combined
unnormalized weight `c^2/2`, while the central width-two interval contributes
`2c^2`. Normalization therefore makes the central fraction
`2 / (2 + 1/2) = 4/5`. This calculation audits the statement; the two substantive
Lean proof bodies intentionally remain `by sorry` at the autoformalize stage.

## Goal-faithfulness audit

Neither `4/5`, `0.80`, nor answer B is a field of
`SatisfiesBornPositionPhysics` or `MatchesProblemStatementAndFigure`. The first
structure contains only the general square-integrability and Born-density laws;
the second contains only scenario and raster readouts. The target interval is
defined from the figure's `-1` and `1` ticks, but its probability is not fixed by
definition.

`MatchesAnswerChoice` is generic in an arbitrary `AnswerChoice` and merely
compares the independently modeled probability with that choice's displayed
value. It is not a hypothesis of either target and does not define the
probability. The main theorem also retains the substantive equality
`queriedPositionProbability experiment = 4/5` as a separate conclusion.

The physical state is not collapsed to a scalar alias: the coordinate
representative has type `ℝ → ℂ`, and the position observable is represented by
an independent normalized `ProbabilityMeasure ℝ`. Real numbers are used only
for explicitly named coordinate readouts, plotted amplitude readouts, tick
multipliers, and dimensionless probability values, as permitted by the physics
modeling rules.

## Declarations and blueprint labels

The current Lean file contains the following declarations covered by the
chapter's declaration topology:

- `QuantumParticleKind` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-quantumparticlekind`
- `HorizontalAxisQuantity` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-horizontalaxisquantity`
- `PositionAxisUnit` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-positionaxisunit`
- `VerticalAxisQuantity` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-verticalaxisquantity`
- `PositionTick` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-positiontick`
- `AmplitudeTick` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-amplitudetick`
- `WaveFunctionCurveShape` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-wavefunctioncurveshape`
- `expectedPositionTickNanometers` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-expectedpositionticknanometers`
- `expectedAmplitudeTickMultiplier` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-expectedamplitudetickmultiplier`
- `PiecewiseWaveFunctionFigure` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-piecewisewavefunctionfigure`
- `ElectronPositionExperiment` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-electronpositionexperiment`
- `plottedWaveAmplitudePerSqrtNanometer` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-plottedwaveamplitudepersqrtnanometer`
- `queriedRegionNanometers` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-queriedregionnanometers`
- `queriedPositionProbability` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-queriedpositionprobability`
- `SatisfiesBornPositionPhysics` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-satisfiesbornpositionphysics`
- `MatchesProblemStatementAndFigure` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-matchesproblemstatementandfigure`
- `AnswerChoice` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-answerchoice`
- `AnswerChoice.displayedProbability` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-answerchoice-displayedprobability`
- `MatchesAnswerChoice` —
  `def:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-matchesanswerchoice`
- `central_interval_probability` —
  `lem:physics:phyx-mini-0647:phyxminiproblems-problemphyxmini0647-central-interval-probability`
- `problem_phyx_mini_0647` — `thm:physics:phyx_mini_0647:target`

## LeanExplore queries and candidates actually used

Every query was run with `packages: ["Mathlib", "Physlib"]`:

- `quantum wave function square integrable one dimensional Hilbert space`
- `Born rule probability measure density squared norm wavefunction`
- `QuantumMechanics.OneDimension.HilbertSpace.MemHS`
- `MeasureTheory.ProbabilityMeasure`
- `MeasureTheory.Measure.withDensity`
- `Complex.normSq`
- `nanometer length unit`

Source and module information was fetched only for the four declarations used
directly in the model:

- `QuantumMechanics.OneDimension.HilbertSpace.MemHS` (candidate id `390266`),
  module `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic`: its source
  defines membership as `MemLp f 2 MeasureTheory.volume`.
- `MeasureTheory.ProbabilityMeasure` (candidate id `266912`), module
  `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`: its source defines the
  subtype of measures satisfying `IsProbabilityMeasure`, hence total mass one.
- `MeasureTheory.Measure.withDensity` (candidate id `268103`), module
  `Mathlib.MeasureTheory.Measure.WithDensity`: its source gives the measure whose
  value on a measurable set is the lower integral of the density over that set.
- `Complex.normSq` (candidate id `198698`), module
  `Mathlib.Data.Complex.Basic`: its source is the real squared magnitude
  `z.re * z.re + z.im * z.im`.

The natural-language Born-rule query returned `Measure.withDensity` but no
ready-made position-space Born observable for this plotted state.
`LengthUnit.nanometers` was found by the unit query but is a unit-conversion
object, whereas `PositionAxisUnit.nanometers` records the literal axis label and
the coordinates are explicitly named scalar readouts in that unit. Replacing
the label vocabulary with the conversion object would not improve the current
statement and would change an already-reviewed public signature.

Near-miss candidates not used include
`QuantumMechanics.SpaceDHilbertSpace` (unneeded higher-dimensional state space),
`CanonicalEnsemble.physicalProbability` (statistical-mechanics density),
`MeasureTheory.IsProbabilityMeasure` (the bundled `ProbabilityMeasure` better
preserves the observable as data), and `Complex.normSq_eq_norm_sq` (a proof
lemma rather than the density function itself).

## PhysLean/Mathlib names grounded

- PhysLean/Physlib:
  `QuantumMechanics.OneDimension.HilbertSpace.MemHS`.
- Mathlib: `MeasureTheory.ProbabilityMeasure`,
  `MeasureTheory.Measure.withDensity`, and `Complex.normSq`.
- `MeasureTheory.volume`, `ENNReal.ofReal`, `Set.Icc`, and
  `ProbabilityMeasure.toMeasure` were additionally grounded by successful Lean
  elaboration of their actual uses in the assigned file.

## Local abstractions introduced

- `PiecewiseWaveFunctionFigure` preserves the axis roles, printed unit, tick
  labels, amplitude scale, and qualitative curve shape visible in the raster.
- `ElectronPositionExperiment` keeps the complex wavefunction representative
  separate from the normalized position-probability observable.
- `SatisfiesBornPositionPhysics` supplies the missing position-space Born-rule
  interface without containing the requested interval probability.
- `MatchesProblemStatementAndFigure` contains only problem and raster evidence.
- `plottedWaveAmplitudePerSqrtNanometer` encodes the primary-image profile with
  an explicit endpoint convention; it contains no probability or answer label.
- The small inductive vocabularies preserve categorical physical/figure roles
  (particle kind, axis quantity and unit label, ticks, curve shape, and answer
  labels) rather than erasing them to bare scalars.
- `queriedPositionProbability` is a named dimensionless scalar projection of the
  physical probability measure on the requested region.

## Grounding gaps and redraft requests

- No direct Mathlib/Physlib declaration for the position probability of an
  arbitrary one-dimensional wavefunction over a spatial interval was found.
  The grounded `ProbabilityMeasure`/`withDensity` interface is the faithful
  local replacement.
- No semantic redraft is requested. The primary image supports the current
  `-c/2, c, -c/2` profile and the symbolic/numeric target `4/5 = 0.80`.
- `.archon/AGENTS.md` is absent in this checkout. The complete active role file
  `.archon/prover-modes/physics-formalize.md` was read instead.
- The blueprint target environment still lacks `\\leanok`. It was not edited
  because this task's explicit write permissions prohibit modifying blueprint
  chapters; the plan/blueprint agent should add the marker.

## Verification

`archon-lean-lsp` reported successful elaboration with exactly two expected
`declaration uses sorry` warnings, at `central_interval_probability` and
`problem_phyx_mini_0647`, and no failed dependencies. The final command
`lake env lean PhyXMiniProblems/problem_phyx_mini_0647.lean` exited with code 0
and emitted only those same warnings (lines 220 and 233).

---

# Prover result: iteration 018

## Outcome

Closed both proof obligations in
`PhyXMiniProblems/problem_phyx_mini_0647.lean` without changing either
declaration signature:

- `central_interval_probability`
- `problem_phyx_mini_0647`

No `sorry`, `admit`, axiom declaration, `native_decide`, or `sorryAx` remains
in the assigned Lean file.

## Proof summary

The proof rewrites the squared plotted amplitude as a sum of three constant
ENNReal densities on the disjoint plateaus `[-2,-1)`, `[-1,1]`, and `(1,2]`.
The Born-density hypothesis and the bundled probability measure's total mass
give

`c²/4 + 2*c² + c²/4 = 1`,

so `c² = 2/5`. Restricting the density to the queried interval `[-1,1]`
then gives mass `2*c² = 4/5`. The main theorem reuses this lemma and unfolds
the displayed value of answer choice B.

## Verification

- `archon-lean-lsp` diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0647.lean`: exited 0
  with no output.
- Source scan for `sorry`, `admit`, `axiom`, `native_decide`, and `sorryAx`:
  no matches.
- Axiom audit for both proved declarations: only standard
  `propext`, `Classical.choice`, and `Quot.sound`; no warnings.

## Redraft needed

None.

## Blueprint note

The relevant blueprint environments still need `\leanok`. They were not
edited because this prover task explicitly grants write permission only for
the assigned Lean file and this task-result file.

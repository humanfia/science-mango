# Autoformalization result: `problem_phyx_mini_0178.lean`

## Iteration 002 retry resolution

The review gate's exact reason was that the physics target did not explicitly
import Mathlib and therefore had not been checked as a real Lake/Mathlib
formalization. The file now explicitly imports `Mathlib` in addition to
`Physlib.Units.WithDim.Speed`. I also re-audited the complete statement against
the source report and primary image rather than treating the retry as an
import-only change. The image visibly has fixed supports, endpoint nodes, and
four antinodes; the source states the fourfold tension change and answer D.

## Assumption/target split

### Governing laws

- `ObeysTransverseStringWaveSpeedLaw` states the stretched-string wave-speed
  law as `v ^ 2 * μ = T`, using SI readouts of dimensionful speed, linear mass
  density, and tension. It is quantified over both string states and does not
  specify a numerical speed ratio.
- `ObeysFixedEndStandingWaveLaw` states `2 * L * f = n * v` for any modeled
  state that is a standing wave with nodes at both endpoints and a positive
  number of antinodes. It does not select four antinodes or a frequency ratio.
- `HasPositivePhysicalData` supplies the strict positivity needed to exclude
  degenerate zero-length, zero-density, zero-speed, zero-tension, or
  zero-frequency configurations.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts and setup conditions

- `StringEndpoint.left` and `StringEndpoint.right` represent the two fixed
  supports shown in the image.
- `MatchesInitialFigure` records that the initial configuration is a standing
  wave, has nodes at both fixed supports, and has the four visibly separated
  antinodes in the primary image.
- `IsRequiredFourAntinodeMode` records the condition posed by the question:
  after the change, the string is again in a fixed-end standing-wave mode with
  four antinodes.
- `TensionIncreasedByFour` records the stated physical change
  `T_after = 4 • T_initial` as an equality of dimensionful tensions.
- `VibratingStringSetup.length` and `linearMassDensity` are shared between
  states, expressing that the same string and fixed-end geometry are retained.

### Current target conclusions

- `waveSpeed_after_fourfold_tension` derives the intermediate physical
  relation `v_after = 2 • v_initial`.
- `frequency_for_four_antinodes_after_fourfold_tension` concludes
  `f_after = 2 • f_initial`, which is answer D and formalizes blueprint label
  `thm:physics:phyx_mini_0178:target`.

## Goal-faithfulness audit

The sought frequency-doubling equality appears only in the conclusion of
`frequency_for_four_antinodes_after_fourfold_tension`. No setup field,
governing-law predicate, figure predicate, or hypothesis contains that
equality. The intermediate speed-doubling result is likewise a theorem
conclusion rather than a premise of the main theorem.

The fourfold tension equality is source data, while the two laws are uniform
relations over both states. Requiring the final configuration to have four
antinodes is the mode condition under which the question asks for a frequency;
it does not determine the numerical frequency without the wave-speed and
fixed-end mode laws. The initial and final modes share length and linear mass
density through common setup fields instead of assuming a derived ratio.

`answerFrequencyFactor` faithfully records all four displayed choices, but it
is not used in any theorem hypothesis or conclusion. In particular, unfolding
the metadata value for choice D cannot prove the substantive physical target.

## Declarations created

- Physical labels: `StringState`, `StringEndpoint`, and `AnswerChoice`.
- Unit-independent quantities: `DimLength`, `DimFrequency`, `DimTension`,
  `DimLinearMassDensity`, the grounded Physlib type `DimSpeed`, and the generic
  scalar projection `siReadout`.
- Model data: `VibratingStringSetup`.
- Figure and requested-mode predicates: `MatchesInitialFigure` and
  `IsRequiredFourAntinodeMode`.
- Physical premises: `TensionIncreasedByFour`,
  `ObeysTransverseStringWaveSpeedLaw`, `ObeysFixedEndStandingWaveLaw`, and
  `HasPositivePhysicalData`.
- Multiple-choice metadata: `answerFrequencyFactor`.
- By-sorry declarations: `waveSpeed_after_fourfold_tension` and
  `frequency_for_four_antinodes_after_fourfold_tension`.
- Blueprint correspondence:
  `frequency_for_four_antinodes_after_fourfold_tension` formalizes
  `thm:physics:phyx_mini_0178:target`; the wave-speed theorem is the explicit
  intermediate implied by the same physical argument.

## LeanExplore queries and candidates

Every LeanExplore query used `packages: ["Mathlib", "Physlib"]`.

- The natural-language query
  `fixed-end standing wave string frequency tension linear mass density wave speed`
  found general harmonic-wave declarations but no fixed-string mode or
  stretched-string tension law.
- Likely-name and dimensional queries were
  `DimSpeed DimFrequency DimForce linear mass density dimensionful physical quantity`,
  `DimFrequency`, `DimForce`, and
  `linear mass density physical units mass per length`.
- Used candidate `DimSpeed` (ID 394481); its fetched source gives
  `Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)` and its fetched module is
  `Physlib.Units.WithDim.Speed`.
- Used candidate `Dimensionful` (ID 394284); fetched source identifies it as
  the subtype of unit-choice readout functions satisfying `HasDimension`, and
  its module is `Physlib.Units.Basic`.
- `Dimension.L𝓭` (ID 394324), `Dimension.M𝓭` (ID 394336), and
  `UnitExamples.NewtonsSecondWithDim'` (ID 394342) grounded the custom length,
  mass-per-length, inverse-time, and force dimension expressions.
- Inspected and rejected near-match
  `ClassicalMechanics.transverseHarmonicPlaneWave` (ID 385509): its fetched
  source is a free-space time-harmonic plane wave and has neither fixed
  endpoints nor a tension/linear-density law.
- Inspected and rejected near-match `FluidDynamics.MassDensity` (ID 386034):
  its fetched source is a spatial scalar field, not a dimensionful linear mass
  density for a string.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `DimSpeed`, `Dimension.L𝓭`,
  `Dimension.T𝓭`, `Dimension.M𝓭`, and `UnitChoices.SI`.
- Mathlib/core data used through the explicit `Mathlib` import: `NNReal`, `ℝ`, `ℕ`,
  `Real.sqrt`, scalar multiplication, powers, order, and equality.

## Local abstractions introduced

- Dedicated dimensionful aliases were introduced for length, ordinary
  frequency, tension, and linear mass density because no matching dedicated
  Physlib aliases were found. They use `Dimensionful (WithDim d NNReal)`, not
  transparent scalar aliases, and their dimensions are respectively length,
  inverse time, force, and mass per length.
- `VibratingStringSetup` distinguishes the two physical states while sharing
  intrinsic string length and linear density. Its standing-wave, endpoint-node,
  and antinode-count fields retain the physical and figure roles rather than
  encoding the desired frequency.
- The two local law predicates are the smallest interfaces needed for the
  textbook stretched-string and fixed-end standing-wave relations absent from
  the searched libraries.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration was found for fixed-end string harmonics,
  antinode counts, the transverse string law `v = sqrt (T / μ)`, or dedicated
  dimensionful tension and linear-density types. The local dimensionful types
  and uniformly quantified law predicates should remain unless such APIs are
  added later.
- `.archon/AGENTS.md` is absent in this checkout. The task instructions and
  `.archon/prover-modes/physics-formalize.md` were followed; the archived
  project role file was also consulted for the prover permission discipline.
- The requested `archon dag-query` navigation command could not be run because
  `archon` is not available on `PATH` in this runtime.
- The blueprint theorem currently has no `\\lean{...}` declaration link. The
  blueprint was not edited because the explicit write permissions restrict
  this prover to the assigned Lean file and this report. A blueprint owner
  should link
  `PhyXMiniProblems.ProblemPhyXMini0178.frequency_for_four_antinodes_after_fourfold_tension`;
  the marker-sync/blueprint owner can then apply `\\leanok` to
  `thm:physics:phyx_mini_0178:target`.

## Verification

- `archon-lean-lsp` diagnostics succeeded with only the two expected
  `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0178.lean` exited with
  code 0 in the explicit Mathlib/Physlib project environment and reported the
  same two expected warnings.
- The project's default `lake build` completed successfully. The problem file
  itself is not registered as a named Lake module target, so its direct
  compilation is evidenced by the preceding `lake env lean` command.

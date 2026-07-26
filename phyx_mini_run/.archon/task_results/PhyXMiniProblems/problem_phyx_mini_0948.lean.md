# Autoformalization result: `problem_phyx_mini_0948.lean`

## Assumption/target split

### Governing laws

- The total wire mass is the linear mass density times the rectangular perimeter:
  `m = λ · 2 · (L + h)`.
- The magnetic torque magnitude about the pivot is
  `τ_B = B · I · L · h · cos θ`.
- The gravitational torque magnitude about the pivot is
  `τ_g = m · g · (h / 2) · sin θ`.
- Static rotational equilibrium imposes `τ_B = τ_g`.
- General signed-axis cross-product/right-hand laws relate the current-oriented
  reference normal, magnetic-field direction, magnetic-torque direction, and
  the shown swing direction.
- The applied Physlib magnetic vector field is uniform in norm and signed-axis
  direction over a nonempty field region.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- The loop is rectangular and pivoted without friction about edge `ab`.
- The image shows `x`, `y`, and `z`; `ab` points along positive `z` from `a` to
  `b`; the reference transverse side points along negative `y` from `b` to `c`.
- The current follows `a → b → c → d → a`, and the depicted swing is positive
  about `z`.
- The edge labels are `6.00 cm` and `8.00 cm`; the angle marker is `30.0°`.
- The wire linear mass density is `0.15 g/cm`, the current is `8.2 A`, and the
  textbook near-Earth gravitational acceleration is `9.8 m/s²`.
- The unknown field is parallel to the `y`-axis; this restricts it to either
  signed `y` direction and does not select the answer sign.

### Current target conclusions

- The magnitude lies within the strict half-millitesla rounding interval around
  answer choice B, `0.024 T`.
- The field direction is positive `y`.

## Goal-faithfulness audit

Neither `0.024 T` nor positive `y` occurs in a hypothesis, apparatus field,
physics-law field, or figure-evidence field. `MatchesProblemDescription` says
only that the unknown field is parallel to the unsigned `y`-axis. The sign is
derived on the conclusion side from the shown current, the positive-`z` swing,
and general cross-direction laws. The magnitude is derived on the conclusion
side from independent dimensionful observables and the mass/torque/equilibrium
laws.

`MagnitudeRoundsToChoice` is a general relation parameterized by all four
answer choices; unfolding it does not prove that choice B is correct. The
general exact field formula is itself a lemma conclusion, not an assumed law.

## Declarations created and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0948:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0948.balancing_magnetic_field`.
- `equilibrium_field_magnitude_formula` states the exact scalar consequence
  `B = λ (L + h) g tan θ / (I L)` before numerical rounding.
- Dimensionful magnitude types were added for magnetic flux density, current,
  length, mass, linear mass density, acceleration, and torque, together with
  named scalar unit readouts.
- `RectangularLoopFigure`, `PivotedCurrentLoopSetup`, and the scenario/law
  structures preserve the apparatus, figure labels, spatial orientation,
  physical laws, and independent observables.
- `AnswerChoice.fieldMagnitudeInTeslas` records all four displayed choices;
  `MagnitudeRoundsToChoice` models their stated three-decimal precision.

The blueprint theorem environment was not edited because this task explicitly
permits writes only to the assigned Lean file and this result file.

## LeanExplore queries and candidates used

- Natural-language query: `uniform magnetic field vector and magnetic torque on
  a current loop` with packages `Mathlib`, `Physlib`. This found
  `Electromagnetism.MagneticField`; no current-loop torque law was returned.
- Likely-name query: `Electromagnetism.MagneticField` with the same package
  filter. Source, module, and docstring were fetched for declaration id `385560`.
- Natural-language query: `dimensionful physical quantity SI units mass length
  current magnetic flux density`. This found `Dimension`, `Dimensionful`,
  `UnitChoices`, and `UnitChoices.SI`.
- Likely-name query: `Dimensionful WithDim UnitChoices SI`, followed by the
  likely-name query `WithDim`. Source/module information was fetched for
  `Dimensionful` (id `394284`), `UnitChoices.SI` (id `394270`), and `WithDim`
  (id `394425`).

## Physlib/Mathlib names grounded

- `Electromagnetism.MagneticField 3` from
  `Physlib.Electromagnetism.Basic`, with signature
  `Time → Space 3 → EuclideanSpace ℝ (Fin 3)`.
- `Dimensionful` and `UnitChoices.SI` from `Physlib.Units.Basic`.
- `WithDim` from `Physlib.Units.WithDim.Basic`.
- Physlib dimension constructors `M𝓭`, `L𝓭`, `T𝓭`, and `C𝓭`.
- Mathlib `NNReal`, `EuclideanSpace`, `Real.sin`, `Real.cos`, `Real.tan`, and
  `Real.pi`.

## Local abstractions introduced

- `SignedAxisDirection`, `SignedAxisDirection.axis`, and
  `SignedAxisDirection.cross?` preserve the six qualitative spatial directions
  and the ordinary right-hand rule. They are linked to the actual Physlib field
  through `HasSignedAxisDirection`, which constrains the three real components.
- The dimensionful magnitude aliases use `Dimensionful (WithDim d NNReal)`;
  they are not transparent scalar aliases. Real-valued functions are explicitly
  named unit readouts only.
- Local governing-law structures were introduced for rectangular-wire mass,
  pivot torque magnitudes, direction laws, and rotational equilibrium. Each law
  relates independent apparatus observables and none states the requested
  numerical result.

## Grounding gaps

- LeanExplore exposed a Physlib spacetime-dependent magnetic vector field but
  no library theorem for the torque on a rigid rectangular current loop or its
  gravitational pivot equilibrium. The faithful local law interfaces above
  therefore fill that gap.
- `Electromagnetism.MagneticField` is real-vector-valued rather than itself
  dimension-tagged. The formalization keeps a separate dimensionful flux-density
  magnitude and calibrates the vector-field norm to that magnitude over the
  uniform region.
- The expected `.archon/AGENTS.md` and the advertised `archon` executable were
  absent in this checkout. The available `.archon/prover-modes/physics-formalize.md`
  was read and followed.

## Verification

- `archon-lean-lsp` diagnostics report only the two expected `sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0948.lean` succeeds with
  those same two warnings.
- The instantiated scalar formula evaluates to approximately
  `0.024150139309 T`, an error of `0.000150139309 T` from the displayed
  `0.024 T`, within the modeled `0.0005 T` rounding tolerance.
- A trailing-whitespace scan passes for both permitted output files.

## Redraft request

- A blueprint-authorized follow-up should add
  `\lean{PhyXMiniProblems.ProblemPhyXMini0948.balancing_magnetic_field}` and
  `\leanok` to `thm:physics:phyx_mini_0948:target`; this agent was expressly
  forbidden from editing blueprint chapters.

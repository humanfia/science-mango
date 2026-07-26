## Assumption/target split

- Governing laws: the wavefunction representative is in PhysLean's one-dimensional
  Hilbert-space domain (`HilbertSpace.MemHS`); it is normalized by the integral of
  `Complex.normSq`; and `positionProbability` applies the Born rule by integrating
  that density over the queried interval.
- Previous-part results: none; the source report lists no previous parts.
- Figure/data readouts: positions are real coordinate readouts in millimetres; the
  walls are at `-4 mm` and `4 mm`; the queried endpoints are `-2 mm` and `2 mm`;
  the plotted amplitude scale `c` is positive; the wavefunction is zero strictly
  outside the walls and equals the real linear profile `c*x/4` between them, hence
  has endpoint values `-c` and `c` and passes through the origin.
- Current target conclusions: the Born probability on `[-2 mm, 2 mm]` is exactly
  `1/8`, and it rounds half-up to `13/100 = 0.13`, identifying answer choice C.

## Goal-faithfulness audit

Neither `1/8` nor `13/100` occurs in any hypothesis, premise structure, or physics-law
definition. `positionProbability` is a generic Born-rule definition for arbitrary
wavefunctions and endpoints, and `RoundsToHundredth` is a generic rounding relation.
The normalization and graph equations are setup facts; the requested central-interval
probability remains entirely on the conclusion side of `central_interval_probability`.

The wavefunction is not collapsed to a scalar alias: it is a complex-valued position
amplitude with PhysLean's square-integrability predicate. Real numbers are used only
for explicitly named millimetre coordinate readouts, the figure's real amplitude
scale, and dimensionless probabilities.

## Declarations and blueprint coverage

- `PhyXMini0506.leftWallMillimetres`, `rightWallMillimetres`,
  `queryLowerMillimetres`, and `queryUpperMillimetres`: figure geometry/readout helpers.
- `PhyXMini0506.positionProbability`: generic position-space Born-rule interval
  probability.
- `PhyXMini0506.RoundsToHundredth`: generic nearest-hundredth relation.
- `PhyXMini0506.central_interval_probability`: formalizes
  `thm:physics:phyx_mini_0506:target`.

The theorem statement is ready for the blueprint's `\\leanok` marker. The blueprint
was not edited because the prover's write permissions explicitly restrict edits to
the assigned Lean file and this result report.

## LeanExplore grounding

Queries used (all with packages `["Mathlib", "Physlib"]`):

- `quantum mechanics wavefunction Born rule probability integral squared norm over a spatial region`
- `MeasureTheory.integral Icc interval integral norm squared complex function`
- `QuantumMechanics.SpaceDHilbertSpace one dimensional position wavefunction`
- `Complex.normSq absolute square complex number`
- `QuantumMechanics.OneDimension.HilbertSpace.MemHS square integrable function`
- `probability from normalized wavefunction integral over measurable set Born rule`

Candidates inspected and used:

- `QuantumMechanics.OneDimension.HilbertSpace` and
  `QuantumMechanics.OneDimension.HilbertSpace.MemHS`, from
  `Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic`.
- `intervalIntegral`, from
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.
- `MeasureTheory.integral`, Mathlib's Bochner integral.
- `Complex.normSq`, from `Mathlib.Data.Complex.Basic`.

The proposed imports and signatures were also checked with an `archon-lean-lsp`
standalone snippet before editing.

## Local abstractions

`positionProbability` was introduced because the searches found the mathematical
integral machinery and PhysLean Hilbert-space model, but no direct position-space
Born-rule probability declaration. It faithfully records the missing governing law
as the interval integral of the squared complex amplitude. `RoundsToHundredth` makes
the dataset's decimal answer precise without asserting the mathematically false exact
equality `1/8 = 0.13`.

## Grounding gaps

No direct Mathlib/PhysLean declaration for Born-rule probability on a spatial interval
was found. PhysLean's `HilbertSpace` is an almost-everywhere equivalence class, whereas
the graph supplies pointwise values, so the theorem uses a function representative
and grounds its physical admissibility with `HilbertSpace.MemHS`.

The requested `.archon/AGENTS.md` is absent in this checkout. The active
`.archon/prover-modes/physics-formalize.md` and the available archived project role
instructions were consulted instead; no redraft is otherwise requested.

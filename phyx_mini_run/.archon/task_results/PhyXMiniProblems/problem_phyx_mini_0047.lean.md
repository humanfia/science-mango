# Autoformalization result: `problem_phyx_mini_0047.lean`

## Assumption/target split

### Governing laws

- `SatisfiesFirstMinimumDiffractionLaws apparatus minima` states the exact
  Fraunhofer single-slit relation `a sin θ = m λ` separately for the upper
  (`m = +1`) and lower (`m = -1`) first minima.
- The same predicate states the slit-to-screen geometry `y = L tan θ` for both
  rays, with all lengths projected to metre readouts.
- Its positivity and angle-branch conditions require positive wavelength,
  slit width, and screen distance; place the upper and lower minima on opposite
  sides of the central `y = 0` axis; and select angles in `(-π/2, π/2)`.
- These are general physical and geometrical laws. They contain no numerical
  value for the requested slit width and select no answer choice.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- `SingleSlitApparatus` preserves the monochromatic laser wavelength, unknown
  slit width, and the figure's slit-to-screen distance along the `x` axis.
- `FirstMinimumGeometry` preserves the signed screen `y` coordinates of the
  first minimum above and below the central bright fringe, together with their
  signed propagation-angle readouts in radians.
- Every wavelength, aperture width, axial distance, and transverse coordinate
  is represented by Physlib's unit-aware
  `Dimensionful (WithDim Dimension.L𝓭 ℝ)`. Only the explicitly named metre,
  millimetre, and nanometre projections are scalar real readouts.
- `HasStatedDiffractionReadouts` records only the independent source data:
  laser wavelength `633 nm`, screen distance `x = 6.0 m`, and full vertical
  separation `32 mm` between the two first-minimum centers.
- `AnswerChoice` and `answerSlitWidthNanometers` retain all four printed
  candidates: A `643 nm`, B `633 nm`, C `639 nm`, and D `533 nm`.

### Current target conclusions

- `slitWidth_eq_recordedAnswerB` concludes that the unknown slit-width
  nanometre readout equals `answerSlitWidthNanometers .B`, i.e. the dataset's
  recorded `633 nm` answer.

## Goal-faithfulness audit

The claim that the slit width is `633 nm` occurs only in the conclusion of
`slitWidth_eq_recordedAnswerB` (through the generic table of all displayed
choices). It is absent from `SingleSlitApparatus`, `FirstMinimumGeometry`,
`HasStatedDiffractionReadouts`, `SatisfiesFirstMinimumDiffractionLaws`, and all
theorem hypotheses. The answer table merely transcribes the source choices;
unfolding it changes the right side of the target to `633` but supplies no fact
about the unknown `apparatus.slitWidth`.

The diffraction predicate states two reusable order equations and two screen
geometry equations. It does not define the slit width as the requested answer,
nor does any local definition make the target true by reflexivity. Physical
lengths use a genuine dimensional Physlib type rather than a transparent real
alias or a one-field scalar wrapper. Thus the recorded conclusion has not been
smuggled into the physical model.

The recorded conclusion is retained honestly even though it conflicts with
the independent readouts and the governing laws. As required for the
autoformalization stage, the declaration remains a `by sorry` target and is
not reported as proved.

## Declarations created and blueprint labels

- Unit-aware quantity/readout declarations: `DimLength`, `lengthValueIn`,
  `metersValue`, `millimetersValue`, and `nanometersValue`.
- Physical and figure structures: `SingleSlitApparatus` and
  `FirstMinimumGeometry`.
- Governing-law predicate: `SatisfiesFirstMinimumDiffractionLaws`.
- Independent data predicate: `HasStatedDiffractionReadouts`.
- Multiple-choice representation: `AnswerChoice` and
  `answerSlitWidthNanometers`.
- Blueprint label `thm:physics:phyx_mini_0047:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0047.slitWidth_eq_recordedAnswerB`.

The blueprint chapter was not edited to add `\leanok`: the task's explicit
write permissions permit changes only to the assigned Lean file and this task
result, and expressly forbid blueprint edits.

## LeanExplore queries/candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `single slit diffraction first minimum wavelength
  slit width` found no geometrical-optics diffraction declaration. Its leading
  results were the unrelated complex-analysis slit-plane API such as
  `Complex.slitPlane`.
- Queries `physical quantity length SI units meter nanometer millimeter` and
  `SI.Length meter` identified the Physlib dimensional/unit API.
- Likely-name queries `LengthUnit.nanometers`, `nanometers length unit`,
  `CarriesDimension.toDimensionful physical length`, and
  `Dimensionful WithDim Dimension.L𝓭` confirmed the relevant dimensional
  declarations.
- Query `Real.tan arctan sin geometry` identified Mathlib's scalar trigonometric
  functions used for the fixed two-dimensional ray geometry.

Source, module, and docstring were fetched before use for:

- `LengthUnit` (id 393137), `LengthUnit.meters` (393154),
  `LengthUnit.millimeters` (393159), and `LengthUnit.nanometers` (393157);
- `Dimensionful` (394284), `WithDim` (394425), `Dimension.L𝓭` (394324), and
  `UnitChoices.SI` (394270);
- `Real.sin` (128819) and `Real.tan` (128821).

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `WithDim.val`, `Dimension.L𝓭`,
  `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, `LengthUnit.meters`,
  `LengthUnit.millimeters`, and `LengthUnit.nanometers`.
- Mathlib: `Real.sin`, `Real.tan`, `Real.pi`, real arithmetic, and real order.

## Local abstractions introduced

- `SingleSlitApparatus` distinguishes the laser wavelength, physical aperture
  width, and axial screen distance instead of collapsing the apparatus to a
  tuple of unrelated scalar numbers.
- `FirstMinimumGeometry` preserves the image's `x`/`y` geometry and keeps the
  two signed first-minimum rays distinct.
- `SatisfiesFirstMinimumDiffractionLaws` is the smallest local interface found
  necessary to state the missing single-slit law and screen geometry. Its two
  order equations are independent governing laws and do not assume the
  requested numerical width.
- `HasStatedDiffractionReadouts` isolates direct source/image data from both
  the physical laws and the theorem conclusion.

## Grounding gaps and redraft requests

- LeanExplore exposed no installed Mathlib/Physlib API for Fraunhofer
  single-slit diffraction, optical minima, or aperture-width inference. The
  faithful local predicate above fills this gap.
- The blueprint contains the physics marker but no informal calculation beyond
  the generic autoformalization instruction. The primary image was therefore
  inspected; it confirms that the `32 mm` bracket is the full separation
  between the two minima across the central axis.
- **Redraft requested:** the recorded answer `633 nm` is inconsistent with the
  stated experiment. The symmetric first-minimum laws give a half-separation
  `y = 16 mm` and hence `tan θ = y/L = 1/375`. Therefore
  `sin θ = 1 / sqrt(140626)` and the exact model gives
  `a = 633 * sqrt(140626) nm`, approximately `237375.844 nm = 237.376 μm`.
  Even the usual small-angle calculation gives `237.375 μm`. None of the four
  printed nanometre choices is compatible with the model, so the recorded
  target should be corrected upstream before the proof stage.
- The requested `.archon/AGENTS.md` and initial assigned Lean file were absent.
  The user-provided role instructions, `.archon/prover-modes/physics-formalize.md`,
  `PROGRESS.md`, source report, blueprint, and image supplied the applicable
  context. Consequently there were no file-specific `/- USER: ... -/` comments
  to apply.
- The `archon` executable was not available on `PATH`, so the optional DAG query
  could not be run. The source report independently confirms there are no
  previous parts.

## Verification

- `archon-lean-lsp` diagnostics report one expected `declaration uses sorry`
  warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0047.lean` exits with code
  0 and the same single expected warning.

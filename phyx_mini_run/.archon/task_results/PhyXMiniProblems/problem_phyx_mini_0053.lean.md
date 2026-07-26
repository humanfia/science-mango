# Autoformalization result: `problem_phyx_mini_0053.lean`

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
was applied. The exact iteration-003 gate reason is that the target lacked a
genuine post-formalization result naming the searches and candidates actually
used, grounded library declarations, local abstractions, grounding gaps, and
the source/law/answer split. This report supplies that evidence after a fresh
audit. Because the gate identified missing evidence rather than a semantic
failure, and the audit found no physical defect, the existing Lean statement
was preserved. It imports `Mathlib` and `Physlib.Units.WithDim.Basic` and
compiles in the Lake/Mathlib environment.

The requested `.archon/AGENTS.md` is absent from this checkout. I used the
injected role instructions and read `.archon/prover-modes/physics-formalize.md`
in full. The assigned Lean file contains no file-specific `/- USER: ... -/`
comment.

## Assumption/target split

### Governing laws

- `ObeysSignedThinLensEquation` states the signed paraxial thin-lens law
  `1/f = 1/s + 1/s'` in the denominator-free, dimensionally homogeneous form
  `f * (s + s') = s * s'`. It is required in every `UnitChoices` system.
- `ObeysTransverseMagnificationLaw` states the standard signed relation
  `m = -s'/s` and the transverse-height interpretation `h_i = m h_o`, again
  for arbitrary unit choices where appropriate.
- `UsesCartesianSignConvention` relates the signed focal length to the
  positive focal-length magnitude and defines signed object/image distances
  from independent axial figure positions. It does not assign the requested
  image distance or magnification.
- `HasPhysicalSignConfiguration` selects the depicted diverging-lens branch:
  positive focal magnitude and object distance, negative signed focal and
  image distances, and positive object height.

### Previous-part results

- None. The source report has `previous_parts: []`, and no previous result is
  assumed by the target theorem.

### Figure/data readouts

- `MatchesPrimaryFigure` records a diverging lens, a virtual upright reduced
  image, a horizontal principal axis, focal-length magnitude `50 cm`, and
  object distance `100 cm`.
- It records axial positions for the object base (`-100 cm`), left focus
  (`-50 cm`), lens center (`0 cm`), and right focus (`50 cm`). The virtual
  image position is constrained only to lie strictly between the left focus
  and lens; it is not assigned the derived value `-100/3 cm`.
- `FigurePoint` preserves the five labeled geometric roles. `FigureRayLabel`
  preserves the ray labels `a` and `b`, and `MatchesPrimaryFigure` records
  that both are drawn.
- The primary image was inspected directly. The circled `4`, `5`, and `6`
  are callout markers rather than height/distance measurements, so no false
  values are assigned to object height, image height, or image position.
- `AnswerChoice.magnification` transcribes every displayed option: A `0.49`,
  B `0.33`, C `0.14`, and D `0.84`.

### Current target conclusions

- `signedImageDistanceInCentimeters_eq_neg_hundred_div_three` concludes the
  intermediate signed virtual-image distance `s' = -100/3 cm`.
- `magnification_eq_one_third` concludes the exact upright magnification
  `m = 1/3`.
- `problem_phyx_mini_0053` concludes both exact magnification `1/3` and that
  answer B's `0.33` is a nearest-hundredth readout of it.

## Goal-faithfulness audit

- No premise field states `s' = -100/3`, `m = 1/3`, or that answer B is
  correct. These numerical relations occur only in lemma/theorem conclusions.
- The governing magnification relation `m = -s'/s` is a general physical law,
  not the target value. Since the signed image distance is independently
  unknown before applying the thin-lens equation, this law does not smuggle
  `m = 1/3` into the hypotheses.
- The sign assumptions choose the physical branch but do not determine either
  target magnitude. The image-position interval likewise does not determine
  `-100/3` by itself.
- `AnswerChoice.magnification` is a table of all source options, while
  `IsNearestHundredthReadout` is a genuine representability-and-error-bound
  predicate. Neither definition preselects B or unfolds to the target.
- Physical lengths use Physlib's unit-coherent `Dimensionful (WithDim L𝓭 ℝ)`;
  only explicitly named centimeter readouts and the dimensionless
  magnification use real scalars.

## Source/law/answer audit

- The generated auxiliary caption incorrectly says that the image is inverted
  and on the right. The primary image instead shows the reduced upright image
  on the left, between the left focal point and the diverging lens. The Lean
  model follows the primary image, as required.
- With Cartesian signs, the pictured data give `f = -50 cm` and `s = 100 cm`.
  The signed thin-lens law gives
  `-50 * (100 + s') = 100 * s'`, hence `s' = -100/3 cm`.
- The transverse law then gives `m = -s'/s = 1/3`. Its distance from `0.33`
  is `1/300`, which is at most the half-hundredth tolerance `1/200`.
  Therefore the recorded answer B is physically consistent.

## Declarations present and blueprint labels

All names below are in namespace `PhyXMiniProblems.ProblemPhyXMini0053`.

| Lean declaration | Blueprint label |
|---|---|
| `LengthQuantity` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-lengthquantity` |
| `centimeterUnitChoices` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-centimeterunitchoices` |
| `lengthInCentimeters` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-lengthincentimeters` |
| `ThinLensKind` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-thinlenskind` |
| `GeometricalImageKind` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-geometricalimagekind` |
| `ImageOrientation` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-imageorientation` |
| `PrincipalAxisOrientation` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-principalaxisorientation` |
| `FigurePoint` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-figurepoint` |
| `FigureRayLabel` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-figureraylabel` |
| `DivergingLensSetup` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-diverginglenssetup` |
| `MatchesPrimaryFigure` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-matchesprimaryfigure` |
| `UsesCartesianSignConvention` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-usescartesiansignconvention` |
| `HasPhysicalSignConfiguration` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-hasphysicalsignconfiguration` |
| `ObeysSignedThinLensEquation` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-obeyssignedthinlensequation` |
| `ObeysTransverseMagnificationLaw` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-obeystransversemagnificationlaw` |
| `AnswerChoice` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-answerchoice` |
| `AnswerChoice.magnification` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-answerchoice-magnification` |
| `IsNearestHundredthReadout` | `def:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-isnearesthundredthreadout` |
| `signedImageDistanceInCentimeters_eq_neg_hundred_div_three` | `lem:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-signedimagedistanceincentimeters-eq-neg-hundred-div-three` |
| `magnification_eq_one_third` | `lem:physics:phyx-mini-0053:phyxminiproblems-problemphyxmini0053-magnification-eq-one-third` |
| `problem_phyx_mini_0053` | `thm:physics:phyx_mini_0053:target` |

The target and both helper lemmas are ready for blueprint statement `\leanok`
markers. The chapter was not edited because this lane's explicit write
permissions prohibit blueprint changes; marker synchronization is left to the
blueprint-authorized pass.

## LeanExplore queries/candidates actually used

Every query passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `paraxial signed thin lens equation focal length
  object distance image distance` returned Mathlib's unrelated `signedDist`,
  thin-category, and homothety declarations. No thin-lens equation was found.
- Natural-language query `transverse magnification image distance divided by
  object distance geometrical optics` returned unrelated homothety/distance
  declarations and no compatible optics law.
- Natural-language query `Dimensionful WithDim physical quantities units`
  found `Dimensionful`, `CarriesDimension.toDimensionful`,
  `UnitChoices.dimScale`, and `WithDim.val_add`.
- Likely-name query `UnitChoices SI LengthUnit.centimeters` found
  `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, and
  `LengthUnit.centimeters`.
- Likely-name query `WithDim` found the exact `WithDim` type and its
  dimensional operations.
- Likely-name query `L𝓭 length dimension` found `Dimension.L𝓭`.
- Source, module, and docstring data were fetched for every selected declaration:
  `Dimensionful` (`Physlib.Units.Basic`), `UnitChoices` and
  `UnitChoices.SI` (`Physlib.Units.Basic`), `WithDim`
  (`Physlib.Units.WithDim.Basic`), `Dimension.L𝓭`
  (`Physlib.Units.Dimension`), and `LengthUnit.centimeters`
  (`Physlib.SpaceAndTime.Space.LengthUnit`).

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`,
  `UnitChoices.SI`, and `LengthUnit.centimeters`.
- Mathlib: `ℝ`, `ℤ`, real arithmetic/order/division, and absolute-value
  notation used by the nearest-hundredth predicate. The direct `Mathlib`
  import resolves the review gate's exact complaint and the Lake compilation
  verifies these names in the real project environment.

## Local abstractions introduced

- Mathlib/Physlib supplied no compatible geometrical-optics thin-lens or
  transverse-magnification declaration. The two local law predicates are the
  smallest faithful replacements: they state standard governing relations
  and contain no target numerical answer.
- The finite inductive types preserve lens/image/orientation, labeled-point,
  principal-axis, ray-label, and answer-choice roles from the scenario and
  primary image; they are not scalar stand-ins for physical quantities.
- `DivergingLensSetup` keeps dimensionful focal lengths, distances, positions,
  and heights distinct from the dimensionless magnification.
- `MatchesPrimaryFigure`, `UsesCartesianSignConvention`, and
  `HasPhysicalSignConfiguration` separate raw readouts, sign bookkeeping, and
  physical branch conditions instead of hiding them in answer-producing local
  definitions.

## Grounding gaps and redraft requests

- No reusable thin-lens or transverse-magnification API appeared in the
  Mathlib/Physlib searches, so the documented local predicates are necessary.
- The advertised `archon dag-query` commands could not be run because
  `archon` is not on `PATH` in this runtime. The source report independently
  confirms that there are no previous parts.
- `.archon/AGENTS.md` is absent. The injected role instructions, the complete
  local `physics-formalize` mode, and the archived same-project role file were
  used instead.
- The auxiliary caption should be corrected to agree with the primary image:
  the image is upright, virtual, reduced, and on the object side. It should
  also identify circled 4/5/6 as callout markers rather than measurements.
- The blueprint states the two intermediate results but its proof prose is
  generic. A plan pass should flesh it out with the signed-lens derivation
  recorded above. `\leanok` remains deterministic sync bookkeeping.

## Verification

- `archon-lean-lsp` reports successful elaboration with exactly three expected
  `declaration uses sorry` warnings, on the two helper lemmas and target
  theorem, and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0053.lean` exits `0` with
  exactly those same three warnings.

## Prover result — iteration 012

All three proof obligations are closed without changing any declaration
signature:

- `signedImageDistanceInCentimeters_eq_neg_hundred_div_three` specializes the
  dimensionful thin-lens law to `centimeterUnitChoices`, projects the resulting
  `WithDim` equality to its real value, substitutes the figure readouts
  `f = -50` and `s = 100`, and solves the resulting linear equation.
- `magnification_eq_one_third` applies the preceding image-distance lemma and
  the signed transverse law `m = -s'/s`.
- `problem_phyx_mini_0053` reuses the exact-magnification lemma and verifies
  answer B's integer-hundredths representation and error bound
  `|1/3 - 33/100| = 1/300 ≤ 1/200`.

No redraft is needed. The assigned Lean file contains no `sorry`, `admit`,
custom `axiom`, `sorryAx`, or `native_decide`.

Final verification:

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0053.lean` exited `0`
  without diagnostics.
- `lake build` completed successfully.

The prover lane did not edit the blueprint because its explicit write
permissions allow only the assigned Lean file and this result file. The target
and both helper-lemma environments are ready for `\leanok` synchronization by
the blueprint-authorized pass.

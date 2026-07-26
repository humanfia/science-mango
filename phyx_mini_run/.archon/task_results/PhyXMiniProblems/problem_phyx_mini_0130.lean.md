# Autoformalization result: `problem_phyx_mini_0130.lean`

## Retry disposition

The iteration-001 review rejected this target because it did not explicitly
import Mathlib. This retry adds `import Mathlib` while retaining the Physlib
unit import and the complete physical statement unchanged. The file was then
checked in the actual Lake project.

## Assumption/target split

### Governing laws

- `objectVergenceInPerMeters` gives a finite object the usual reciprocal-distance
  vergence and gives an object at optical infinity zero vergence (parallel
  incident rays).
- `FormsVirtualImageAtUnaidedFarPoint` is the myopia prescription criterion:
  the spectacle lens must make distant rays appear to originate at the eye's
  unaided far point. It converts the eye-based far-point distance to a
  lens-based signed virtual-image distance using the stated lens offset.
- `ObeysThinLensEquation` states the signed paraxial relation
  `1/f = Vₒ + 1/dᵢ`.
- `ObeysOpticalPowerLaw` states the general relation `P = 1/f`, with the SI
  power readout measured in inverse metres (diopters).
- `LensKindAgreesWithFocalSign` states the general sign convention that a
  converging lens has positive focal length and a diverging lens has negative
  focal length.

### Previous-part results

- None. The source report's `previous_parts` list is empty.

### Figure/data readouts

- `HasStatedDistanceReadouts` records the 12 cm near point, 17 cm far point,
  and 2 cm lens-to-eye distance as SI readouts of dimensionful lengths.
- `HasPhysicalDistanceOrdering` records positivity and the ordering
  `lens offset < near point < far point`.
- `ViewsDistantObject` records that the requested correction concerns an
  object at optical infinity.
- `MatchesSourceFigure` records the primary image's left-to-right labels
  `O`, `I`, spectacle lens, and eye; the virtual-image status of `I`; the
  12 cm `I`--eye near-point bracket; and the visibly concave/diverging lens.
  The figure configuration is deliberately separate from the distant-vision
  image configuration, whose virtual image is at the 17 cm far point.
- `answerPowerDiopters` transcribes all four printed choices: `-5.3`, `-6.3`,
  `-6.7`, and `-5.6` diopters.

### Current target conclusions

- `signedDistantImageDistance_eq_neg_three_twentieth` concludes that the
  far-point virtual image is 15 cm to the left of the spectacle lens.
- `reciprocalFocalLength_eq_neg_twenty_thirds` concludes that the reciprocal
  focal length is exactly `-20/3 m⁻¹`.
- `problem_phyx_mini_0130` concludes that the correction has exact optical
  power `-20/3` diopters and that choice C's `-6.7 D` is a nearest-tenth
  readout of that value.

## Goal-faithfulness audit

The exact target power `-20/3`, the derived 15 cm signed image distance, and
the assertion that choice C is correct do not occur in
`NearsightedCorrectionSetup`, any governing-law predicate, any data/figure
predicate, or any theorem hypothesis. The only numerical assumptions are the
independent source values 12 cm, 17 cm, and 2 cm. The far-point image predicate
states the physical correction requirement, not the requested power.

`answerPowerDiopters` is a neutral transcription of every candidate, while
`IsNearestTenthReadout` is a generic rounding relation and does not select C.
The three substantive numeric conclusions remain lemma/theorem conclusions
with `by sorry` bodies, as required in the autoformalize stage.

Lengths and optical powers are not scalar aliases: they use distinct Physlib
dimensions `L𝓭` and `L𝓭⁻¹` through `Dimensionful (WithDim ... ℝ)`. Optical
infinity, finite object locations, image kind, lens kind, and figure labels
are represented by role-specific inductive types rather than being collapsed
to real-number placeholders.

## Declarations created and blueprint labels

- Dimensional quantities/readouts: `LengthQuantity`,
  `OpticalPowerQuantity`, `lengthInMeters`, and `powerInDiopters`.
- Physical and figure roles: `ThinLensKind`, `ImageKind`, `FigurePoint`,
  `ObjectLocation`, `ClearVisionRange`, `ThinCorrectiveLens`, and
  `NearsightedCorrectionSetup`.
- Setup/law predicates: `HasStatedDistanceReadouts`,
  `HasPhysicalDistanceOrdering`, `MatchesSourceFigure`,
  `ViewsDistantObject`, `FormsVirtualImageAtUnaidedFarPoint`,
  `ObeysThinLensEquation`, `ObeysOpticalPowerLaw`, and
  `LensKindAgreesWithFocalSign`.
- Answer model: `AnswerChoice`, `answerPowerDiopters`, and
  `IsNearestTenthReadout`.
- Derived declarations: `signedDistantImageDistance_eq_neg_three_twentieth`
  and `reciprocalFocalLength_eq_neg_twenty_thirds`.
- Blueprint label `thm:physics:phyx_mini_0130:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0130.problem_phyx_mini_0130`.

## LeanExplore queries/candidates actually used

Every query used `packages: ["Mathlib", "Physlib"]`.

- Natural-language queries `paraxial thin lens equation reciprocal focal
  length object distance image distance` and `optical power focal length
  diopter myopia corrective lens` found no matching geometrical-optics law.
  The only physically adjacent result was the general `LengthUnit`; the other
  hits concerned unrelated reciprocals, categorical thinness, or power of a
  point with respect to a sphere.
- Likely-name query `ThinLens opticalPower diopter` likewise found no lens API.
- Dimensional query `Dimensionful WithDim UnitChoices.SI length inverse
  length` found `Dimensionful` (id 394284), `UnitChoices.SI`-related
  declarations, and general length-unit infrastructure.
- Likely-name queries `WithDim`, `UnitChoices.SI`, and `Dimension.L𝓭 inverse
  length` selected `WithDim` (id 394425), `UnitChoices.SI` (id 394270),
  `Dimension.L𝓭` (id 394324), and `Dimension.inv_length` (id 394308).
- Source, module, and documentation were fetched for the final-use candidates
  `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI`.
  The returned modules were `Physlib.Units.Basic`,
  `Physlib.Units.WithDim.Basic`, and `Physlib.Units.Dimension`.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `WithDim.val`, `Dimension.L𝓭`, inverse
  dimension notation `L𝓭⁻¹`, and `UnitChoices.SI`.
- Mathlib (now imported explicitly): real and integer arithmetic, absolute
  value, coercion from `ℤ` to `ℝ`, and real order.

## Local abstractions introduced

- `ObjectLocation` distinguishes optical infinity from finite dimensionful
  object distances, preserving the role of parallel incident rays.
- `ThinLensKind`, `ImageKind`, and `FigurePoint` preserve the optical and
  diagrammatic roles visible in the primary image.
- `ClearVisionRange`, `ThinCorrectiveLens`, and
  `NearsightedCorrectionSetup` keep near/far points, eye/lens geometry, signed
  image distance, focal length, and power physically distinct.
- Local predicates state virtual-image placement, the thin-lens equation, and
  the optical-power law because no matching installed Mathlib/Physlib thin-lens
  API was found.

## Grounding gaps and redraft requests

- LeanExplore exposed no usable API for thin lenses, focal length, virtual
  images, eyeglass prescriptions, or diopters beyond Physlib's general
  dimensional-quantity infrastructure. Faithful local abstractions were used.
- The requested `.archon/AGENTS.md` is absent. The user-provided role
  instructions and `.archon/prover-modes/physics-formalize.md` supplied the
  applicable role. The assigned Lean file was present and contains no
  file-specific `/- USER: ... -/` comments.
- The `archon` executable was not available on `PATH`, so the optional DAG
  query could not run. The source report independently confirms that there are
  no previous parts.
- The auxiliary caption calls the depicted lens convex and says the 12 cm
  mark is between `I` and the lens. The primary image instead visibly shows a
  concave/diverging lens and a bracket from `I` to the eye. The Lean model
  follows the primary image, per the chapter's instruction; the caption should
  be redrafted to match it.
- The blueprint proof block contains only the autoformalization instruction,
  not the promised informal optics derivation. A plan pass should add the
  derivation `17 cm - 2 cm = 15 cm`, `f = -15 cm`, and
  `P = 1/f = -20/3 D`, rounded to choice C.
- The theorem environment is ready for `\\leanok`, but the blueprint was not
  edited because the task's explicit write-permission section allows changes
  only to the assigned Lean file and this task-result file.

## Verification

- `archon-lean-lsp` reports successful elaboration with exactly three expected
  `declaration uses sorry` warnings and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0130.lean` succeeds with
  the same three expected warnings.

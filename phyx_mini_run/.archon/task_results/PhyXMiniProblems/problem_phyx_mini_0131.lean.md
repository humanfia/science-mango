# Autoformalization result: `problem_phyx_mini_0131.lean`

## Review-gate disposition

The exact review-2 rejection was missing post-formalization evidence, not a
semantic defect.  I re-audited the current Lean statement against the source
report, primary image, blueprint, and fresh LeanExplore results and preserved
the statement unchanged.  The source values and Rayleigh law give an
improvement near `8.67`, so displayed choice D (`9×`) is nearest.  Recorded
choice C (`14×`) remains metadata and is not asserted as the physics answer.

## Assumption/target split

### Governing laws

- `SatisfiesRayleighCriterion` states the circular-aperture law
  `θ_H = (61 / 50) * λ / D` using a common arbitrary `LengthUnit`.  It
  determines Hubble's angular resolution without assigning an improvement
  value or selecting an answer.
- `SatisfiesResolutionImprovementLaw` states that the dimensionless
  improvement is the angular-resolution ratio `θ_E / θ_H`.  This is the
  comparison law, not a displayed numerical answer.
- `HasPhysicalResolutionParameters` supplies positivity and small-angle ranges
  for the physical readouts.  It does not identify choice D.

### Previous-part results

- None.  The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemReadouts` records the stated `2.4 m` objective diameter,
  `550 nm` wavelength, and nominal half-arcsecond atmospheric limit, converted
  to radians by `arcsecondsToRadians`.
- `arcsecondsPerDegree = 3600` records the problem's angular conversion, and
  `Real.pi / 180` supplies the standard degree-to-radian conversion.
- `MatchesScenarioAndFigure` records the reflecting Hubble telescope in orbit,
  the Earth telescope within the atmosphere, and the respective diffraction
  and turbulence limitations.
- Direct inspection of `phyx_data/test_image/131.png` supports the encoded
  qualitative readouts: Hubble hardware with a metallic cylindrical body and
  orange solar panels in the foreground, partial Earth with cloud/ocean detail
  in the background, a dark space backdrop, and no text.  The image supplies
  no numerical value.

### Current target conclusion

- `problem_phyx_mini_0131` concludes
  `IsNearestDisplayedImprovementChoice setup .D`: the displayed `9×` option is
  at least as close to the physically derived factor as each other option.

## Goal-faithfulness audit

`TelescopeResolutionSetup.resolutionImprovementFactor` is an unknown
dimensionless result.  No field, premise predicate, governing-law field, or
local definition assigns it `9` or selects D.  Source readouts contain only
source/figure data; the Rayleigh premise supplies only `θ_H = 1.22 λ / D`; and
the comparison premise supplies only the ratio definition.  The nearest-choice
inequalities still have to be derived from those premises.  The definition
`recordedDatasetAnswer := .C` preserves the conflicting dataset label but does
not occur in the theorem target.  Thus no current conclusion is smuggled into
an assumption or made true by unfolding.

## Source/law/answer audit

- Source-supported numerical inputs: `D = 2.4 m`, `λ = 550 nm`, and the
  nominal Earth limit `θ_E = 0.5 arcsec`.
- Standard governing relation: Rayleigh circular-aperture resolution
  `θ_H = 1.22 λ / D`.
- Consequence check: `θ_H ≈ 2.7958e-7 rad ≈ 0.05767 arcsec`, so
  `θ_E / θ_H ≈ 8.67`; among `{7, 12, 14, 9}`, `9` is nearest.
- Dataset answer C is contradicted by this source-supported model and therefore
  is represented only as metadata.  No alternative source law supporting
  `14×` was supplied.

## Declarations and blueprint labels

All declarations are in namespace
`PhyXMiniProblems.ProblemPhyXMini0131`.

| Lean declaration | Blueprint label |
|---|---|
| `LengthQuantity` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-lengthquantity` |
| `lengthReadout` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-lengthreadout` |
| `lengthInMeters` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-lengthinmeters` |
| `lengthInNanometers` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-lengthinnanometers` |
| `arcsecondsPerDegree` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-arcsecondsperdegree` |
| `arcsecondsToRadians` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-arcsecondstoradians` |
| `TelescopeOpticalDesign` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-telescopeopticaldesign` |
| `ObservatoryLocation` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-observatorylocation` |
| `ResolutionLimitation` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-resolutionlimitation` |
| `FigureFeature` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-figurefeature` |
| `FigureLocation` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-figurelocation` |
| `TelescopeResolutionSetup` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-telescoperesolutionsetup` |
| `MatchesScenarioAndFigure` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-matchesscenarioandfigure` |
| `MatchesProblemReadouts` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-matchesproblemreadouts` |
| `HasPhysicalResolutionParameters` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-hasphysicalresolutionparameters` |
| `SatisfiesRayleighCriterion` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-satisfiesrayleighcriterion` |
| `SatisfiesResolutionImprovementLaw` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-satisfiesresolutionimprovementlaw` |
| `AnswerChoice` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-answerchoice` |
| `displayedImprovementFactor` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-displayedimprovementfactor` |
| `recordedDatasetAnswer` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-recordeddatasetanswer` |
| `IsNearestDisplayedImprovementChoice` | `def:physics:phyx-mini-0131:phyxminiproblems-problemphyxmini0131-isnearestdisplayedimprovementchoice` |
| `problem_phyx_mini_0131` | `thm:physics:phyx_mini_0131:target` |

## LeanExplore queries and candidates actually used

Every search used package filters `Mathlib` and `Physlib`.

- `Rayleigh criterion angular resolution circular aperture telescope wavelength diameter`
  returned no telescope/diffraction criterion.  The leading candidate,
  `ContinuousLinearMap.rayleighQuotient`, is a spectral-theory quotient and was
  rejected as unrelated.
- `Dimensionful WithDim physical length quantity LengthUnit meters nanometers UnitChoices`,
  `WithDim`, and `Dimension-tagged NNReal physical quantity` grounded
  `Dimensionful`, `WithDim`, and `Dimension.L𝓭` for the physical length type.
- `LengthUnit`, `The definition of a length unit of meters`, and
  `UnitChoices SI unit system physical units` grounded `LengthUnit`,
  `LengthUnit.meters`, `LengthUnit.nanometers`, `UnitChoices`, and
  `UnitChoices.SI` for unit-dependent scalar readouts.
- `nonnegative real NNReal` grounded `NNReal` as the nonnegative carrier.
- `Real.pi radians degrees angular measurement` grounded `Real.pi` and also
  returned `Real.Angle`.  `Real.Angle` was evaluated but not used: angular
  resolution here is a positive, small scalar radian readout whose quotient is
  the requested improvement, whereas a periodic quotient angle would obscure
  those measurement operations.
- Source, module, and docstring data were fetched for the candidates actually
  selected: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit`,
  `LengthUnit.meters`, `LengthUnit.nanometers`, `UnitChoices.SI`, `NNReal`, and
  `Real.pi`.

## PhysLean/Mathlib names grounded

- Physlib/PhysLean: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit`,
  `LengthUnit.meters`, `LengthUnit.nanometers`, `UnitChoices`, and
  `UnitChoices.SI`.
- Mathlib: `NNReal`, `Real.pi`, real absolute-value notation, and ordinary real
  arithmetic/order.
- Imports used: `Physlib.Units.WithDim.Basic` and
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.

## Local abstractions introduced

- `TelescopeOpticalDesign`, `ObservatoryLocation`, `ResolutionLimitation`,
  `FigureFeature`, and `FigureLocation` preserve qualitative physical and
  image roles for which no matching library API exists.
- `TelescopeResolutionSetup` keeps dimensionful lengths separate from scalar
  radian readouts and the dimensionless improvement factor; it does not encode
  the answer.
- `MatchesScenarioAndFigure`, `MatchesProblemReadouts`, and
  `HasPhysicalResolutionParameters` separate image/source evidence and domain
  conditions from governing laws.
- `SatisfiesRayleighCriterion` and `SatisfiesResolutionImprovementLaw` are the
  smallest local interfaces for the two governing relations absent from the
  libraries.
- `AnswerChoice`, `displayedImprovementFactor`, and
  `IsNearestDisplayedImprovementChoice` preserve the multiple-choice estimate
  semantics without treating the recorded label as authoritative physics.

## Grounding gaps and redraft requests

- No Mathlib/Physlib API for circular-aperture Rayleigh resolution or
  atmosphere-limited telescope resolution was found; the faithful local law
  interfaces are therefore necessary.
- No statement redraft is requested.  The current blueprint and Lean theorem
  already state the source-supported D result and retain recorded C only as
  metadata.
- `.archon/AGENTS.md` is absent in this checkout.  The archived project role
  file confirms that provers must not edit blueprint chapters and that
  `sync_leanok` owns routine `\leanok` updates.  Consequently the chapter was
  not edited, consistent with this task's explicit write permissions.
- The prompt says `archon` is on `PATH`, but `archon dag-query` is unavailable
  in this shell.  The target has no theorem dependencies in its blueprint
  `\uses{...}` list, so this does not affect the formalization.

## Verification

- `archon-lean-lsp` reports only the expected warning at the theorem body:
  `declaration uses sorry`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0131.lean` exits successfully
  with the same single expected warning.
- No `/- USER: ... -/` file-specific hint is present.

## Assumption/target split

### Governing laws and physical setup conditions

- `IrradianceQuantity` uses `NNReal`, so every input and transmitted physical irradiance is nonnegative without adding an untyped scalar-intensity primitive.
- `MatchesProblemDescription` records only the source statement that the beam propagates horizontally.
- `SatisfiesIdealPolarizerLaws.unpolarizedTransmission` states the ideal-polarizer law that the unpolarized contribution is halved.
- `SatisfiesIdealPolarizerLaws.malusTransmission` states Malus's law for every plotted polarizer-axis angle `α`: the polarized contribution is `Iₚ cos²(α - θ)`.
- `SatisfiesIdealPolarizerLaws.incoherentAddition` states that the separately transmitted unpolarized and polarized irradiances add to the plotted total irradiance.

### Previous-part results

- None. The source report records `previous_parts: []`.

### Figure/data readouts

- `PolarizerIntensityGraph` retains the horizontal and vertical axis roles, printed units, plotted ranges, and grid metadata.
- `MatchesIntensityGraph` records the horizontal label `α (°)` over `[0, 200]`, the vertical label `I_total (W/m²)` over `[0, 30]`, and the visible grid.
- Its `maximumReadout` records an attained maximum of `25 W/m²` on the plotted interval, and its `minimumReadout` records an attained minimum of `5 W/m²`. These values come from the primary image; the auxiliary caption's “troughs around 10” is inconsistent with the image, whose lowest plotted points lie on the `5 W/m²` grid line.
- `answerIrradianceInWattsPerSquareMeter` records the displayed choices A `20`, B `15`, C `25`, and D `30 W/m²` as answer-table data only.

### Current target conclusions

- `problem_phyx_mini_0105` concludes that the dimensionful incident polarized irradiance `Iₚ` equals `wattsPerSquareMeter 20` and therefore matches answer choice A.

## Goal-faithfulness audit

The value `Iₚ = 20 W/m²` and the selection of choice A occur only in the conclusion of `problem_phyx_mini_0105` (and in the answer-table lookup used by that conclusion). They do not occur in `MatchesProblemDescription`, `SatisfiesIdealPolarizerLaws`, `MatchesIntensityGraph`, or any setup field. In particular, the graph assumptions supply only independently read total-curve extrema, `25` and `5`; the governing laws are generic for every angle and do not mention their difference or the requested answer.

`wattsPerSquareMeter` is a unit constructor, not a definition of the unknown in terms of the desired result. `MatchesPolarizedIntensityAnswer` compares the independently modeled `polarizedInputIp` readout with a selected answer-table entry and is used only on the target side. The substantive conclusion cannot be obtained by unfolding a local definition: it requires showing from Malus's law, the unpolarized-halving law, additive irradiances, and the graph extrema that the peak-to-trough amplitude is `Iₚ`.

## Declarations created and blueprint correspondence

- Blueprint label `thm:physics:phyx_mini_0105:target` corresponds to `problem_phyx_mini_0105`.
- Physical/unit declarations: `IrradianceQuantity`, `irradianceInWattsPerSquareMeter`, `wattsPerSquareMeter`, and `degrees`.
- Figure/setup declarations: `PropagationDirection`, `FigureAxis`, `FigureAxisUnit`, `PolarizerIntensityGraph`, and `MixedBeamPolarizerSetup`.
- Assumption declarations: `MatchesProblemDescription`, `SatisfiesIdealPolarizerLaws`, and `MatchesIntensityGraph`.
- Answer-table declarations: `AnswerChoice`, `answerIrradianceInWattsPerSquareMeter`, and `MatchesPolarizedIntensityAnswer`.

The blueprint chapter was not edited because the task's final write-permission section permits edits only to the assigned Lean file and this result file. The blueprint maintainer should add `\leanok` to `thm:physics:phyx_mini_0105:target` after accepting the formalization.

## LeanExplore queries/candidates actually used

Every query used package filters `Mathlib` and `Physlib`.

- Natural-language query `Malus law polarized light intensity cosine squared polarizer`: no Malus-law declaration was returned; `Real.cos_sq` and an electromagnetic polarization-ellipse result were near misses.
- Natural-language queries `irradiance optical intensity watt per square meter physical quantity`, `SI unit watt per square meter quantity dimensions`, and `physical dimension power energy divided by time`: selected Physlib's dimension infrastructure rather than introducing a scalar optical-intensity alias.
- Likely-name queries `WithDim`, `Dimensionful`, `toDimensionful`, and `Dimension.M𝓭 Dimension.T𝓭`: selected `WithDim`, `Dimensionful`, `CarriesDimension.toDimensionful`, `Dimension.M𝓭`, and `Dimension.T𝓭`.
- Natural-language query `value of Dimensionful quantity in SI units` and likely-name query `WithDim SI value`: confirmed evaluation of a `Dimensionful` quantity at `UnitChoices.SI` and projection through `WithDim.val`.
- Likely-name query `Real.Angle.cos`: selected `Real.Angle` and `Real.Angle.cos` for physical directions modulo `2π`.
- Queries `Set.Icc closed interval` and `NNReal nonnegative real numbers`: selected `Set.Icc` for the plotted domain and `NNReal` for nonnegative irradiance magnitudes.

Source and module details were fetched for the adopted candidates `WithDim`, `Dimension`, `Dimensionful`, `CarriesDimension.toDimensionful`, `UnitChoices.SI`, `Dimension.M𝓭`, `Dimension.T𝓭`, `Real.Angle`, `Real.Angle.cos`, `Set.Icc`, and `NNReal`.

## Physlib/Mathlib names grounded

- Physlib `Dimensionful` and `CarriesDimension.toDimensionful` from `Physlib.Units.Basic`.
- Physlib `WithDim` from `Physlib.Units.WithDim.Basic`.
- Physlib `Dimension.M𝓭` and `Dimension.T𝓭` from `Physlib.Units.Dimension`; `M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹` is the irradiance dimension `mass / time³`, equivalently power per area.
- Physlib `UnitChoices.SI` from `Physlib.Units.Basic` for readouts in `W/m²`.
- Mathlib `NNReal` from `Mathlib.Data.NNReal.Defs`.
- Mathlib `Real.Angle` and `Real.Angle.cos` from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.
- Mathlib `Set.Icc` from `Mathlib.Order.Interval.Set.Defs`.

## Local abstractions introduced

- No ready-made optical irradiance type was found, so `IrradianceQuantity` specializes Physlib's unit-independent, dimension-tagged quantity infrastructure to nonnegative values with physical dimension `mass / time³`. It is not a transparent scalar alias or a one-field scalar wrapper.
- `MixedBeamPolarizerSetup` retains the distinct incident and transmitted polarized/unpolarized components, the physical polarization-plane angle `θ`, the graph-indexed polarizer-axis coordinate `α`, the total transmitted irradiance, and graph metadata.
- `SatisfiesIdealPolarizerLaws` is a faithful local governing-law interface because LeanExplore found no dedicated Malus-law declaration. Splitting halving, Malus transmission, and incoherent addition keeps the physical derivation visible and does not encode the requested numerical answer.
- `MatchesIntensityGraph` represents calibrated extrema with existence plus global bounds over the displayed domain, rather than assuming a peak-to-trough formula already solved for `Iₚ`.

## Grounding gaps and redraft requests

- No Mathlib/Physlib declaration for Malus's law or a dedicated optical irradiance quantity was found. The adopted local law and Physlib dimension specialization preserve their physical content.
- The auxiliary caption says the trough is around `10 W/m²`, but the primary image places its minimum at `5 W/m²`; the formalization follows the instruction to use the image as primary evidence. A future source redraft should correct the caption.
- The chapter exists and is marked `% archon:physics`, but its proof environment contains only autoformalization instructions, not the promised informal physical derivation. A redraft should state `I_total(α) = I₀/2 + Iₚ cos²(α-θ)` and `Iₚ = I_max - I_min = 25 - 5`.
- `.archon/AGENTS.md` was absent, so `.archon/prover-modes/physics-formalize.md` supplied the available role instructions. The requested `archon dag-query` could not run because the `archon` executable was not on this runtime's `PATH`; the source report has no previous parts.
- The assigned Lean file did not exist, so there were no file-specific `/- USER: ... -/` comments to apply; it was created at the assigned path.

## Verification

- `archon-lean-lsp` reports exactly one diagnostic: the expected `declaration uses sorry` warning on `problem_phyx_mini_0105`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0105.lean` exits successfully; its only output is that same expected `sorry` warning.

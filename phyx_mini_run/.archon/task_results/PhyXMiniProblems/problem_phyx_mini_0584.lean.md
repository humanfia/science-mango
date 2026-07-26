# Autoformalization result: `problem_phyx_mini_0584.lean`

## Assumption/target split

### Governing laws

- `SatisfiesInfiniteRectangularWellLaws` states the general two-dimensional infinite-rectangular-well model:
  - the pointwise representative is square-integrable and agrees almost everywhere with the `L²` Hilbert-space state;
  - inside the rectangle it is a nonzero separable product of the `x` and `y` sine modes, and it vanishes outside the hard walls;
  - along either non-nodal bisector probe, the number of reported equal maxima is the quantum number of the varying coordinate;
  - the side length in the varying coordinate is the peak count times the adjacent-peak spacing;
  - the spectrum is `E = h²/(8m) (n_x²/L_x² + n_y²/L_y²)` in coherent SI readouts.
- `HasPhysicalRectangularWellParameters` contains only positivity/nondegeneracy conditions for mass, Planck action, side lengths, quantum numbers, measured spacings, and energy.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesRectangularWellElectronScenario` records an electron in a two-dimensional infinite rectangular well in the `xy`-plane.
- `MatchesPrimaryRectangularWellFigure` records the blue rectangular boundary, dashed vertical and horizontal bisectors, coordinate-axis labels, and the `L_x`/`L_y` side-label assignments seen in image `584.png`.
- `MatchesDetectionProbeReadouts` records three maxima separated by `2 nm` on the vertical line `x = L_x/2`, and five maxima separated by `3 nm` on the horizontal line `y = L_y/2`. It also gives a point-level meaning to “all detection-probability maxima” and “adjacent separation.”
- `UsesElectronReferenceData` records only the electron-mass calibration `9.1093837139e-31 kg`.
- `UsesStandardPlanckConstant` records only `h = 2πℏ`, using Physlib's standard reduced Planck constant.
- `displayedSymbolicEnergyFormula` and `recordedDatasetAnswer` retain the four literal option expressions and recorded label C as source metadata. Neither is a theorem premise.

### Current target conclusions

- `quantumNumbers_from_probe_peak_counts`: `n_x = 5` and `n_y = 3`.
- `sideLengths_from_probe_peak_spacings`: `L_x = 15 nm` and `L_y = 6 nm`.
- `energy_from_probe_spacings`: the exact spacing-only energy formula
  `E = h²/(8m) ((3e-9 m)⁻² + (2e-9 m)⁻²)`.
- `problem_phyx_mini_0584`: the exact standard-constant SI energy and the numerical result `E ≈ 0.135789 eV` with tolerance `1e-6 eV` (equivalently about `2.17557e-20 J`).

## Goal-faithfulness audit

- `stateEnergy`, both quantum numbers, and both side lengths are independent fields of `RectangularWellElectronSetup`; none is defined by the requested result.
- No premise contains `n_x = 5`, `n_y = 3`, `L_x = 15 nm`, `L_y = 6 nm`, the exact target-energy expression, `0.135789 eV`, or a matching-answer predicate.
- The peak-count and peak-spacing rules are general governing relations quantified over both probe lines. The measured values `3`, `5`, `2 nm`, and `3 nm` occur only in the experimental-readout predicate.
- The two-dimensional spectrum is a general law over the setup's independent `h`, `m`, `n_x`, `n_y`, `L_x`, `L_y`, and `E` fields. It does not contain the current target value.
- The literal option-C definition is isolated metadata and is not supplied to any derived lemma or the main theorem.
- The exact and approximate energy conclusions therefore require combining observations, the general well laws, and independent standard-reference data; they cannot be obtained by unfolding a target-shaped definition.

## Declarations and blueprint labels

- Blueprint label `thm:physics:phyx_mini_0584:target` corresponds to Lean theorem `PhyXMiniProblems.ProblemPhyXMini0584.problem_phyx_mini_0584`.
- Supporting declarations without separate blueprint labels:
  - dimensionful quantity/readout definitions;
  - `CoordinateAxis`, `ProbeLine`, `RectangularWellFigure`, `DetectionProbeObservation`, and `RectangularWellElectronSetup`;
  - scenario, image, measurement, calibration, physicality, and governing-law predicates;
  - literal dataset answer metadata;
  - the three derived lemmas listed above.
- The blueprint chapter was not edited to add `\leanok` because the task's explicit write-permission section permits edits only to the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `quantum particle in a two dimensional rectangular infinite potential well energy eigenvalues`:
  - no rectangular-well spectrum was found;
  - near misses included `QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue` and classical kinetic/potential-energy declarations;
  - `DimEnergy` was relevant and used.
- Natural-language query `physical dimensions length mass energy Planck constant SI units`:
  - used `UnitChoices.SI`, `Dimension`, `Dimension.L𝓭`, `DimEnergy`, and `Constants.ℏ`.
- Natural-language query `MeasureTheory probability density maxima wavefunction`:
  - returned generic probability-density declarations and statistical-mechanics densities, but no API for pointwise maxima of a quantum position density along a probe; a faithful local predicate was introduced.
- Likely-name query `Real.pi`:
  - used `Real.pi`.
- Natural-language/likely-name queries `WithDim length dimensional quantity value in SI units`, `DimLength dimensional length quantity`, `DimMass dimensional mass quantity`, and `convert dimensional quantity to real value units`:
  - used the `Dimensionful (WithDim ... ...)` representation and unit-choice evaluation pattern.
- Likely-name query `QuantumMechanics.SpaceDHilbertSpace`:
  - used `QuantumMechanics.SpaceDHilbertSpace 2` and its `MemHS` predicate.
- Likely-name queries `DimEnergy.electronVolt`, `LengthUnit.nanometers`, and `MassUnit.kilograms`:
  - used all three declarations for calibrated readouts.

Source/module data were fetched for the candidates actually used: `Dimension`, `UnitChoices.SI`, `Constants.ℏ`, `DimEnergy`, `Dimension.L𝓭`, `Real.pi`, `QuantumMechanics.SpaceDHilbertSpace`, `DimEnergy.electronVolt`, `LengthUnit.nanometers`, and `MassUnit.kilograms`.

## Physlib/Mathlib names grounded

- Physlib units: `Dimension`, `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `Dimension.M𝓭`, `Dimension.T𝓭`, `UnitChoices.SI`, `LengthUnit.meters`, `LengthUnit.nanometers`, `MassUnit.kilograms`, `DimEnergy`, and `DimEnergy.electronVolt`.
- Physlib quantum mechanics: `QuantumMechanics.SpaceDHilbertSpace`, `QuantumMechanics.SpaceDHilbertSpace.MemHS`, and `Constants.ℏ`.
- Mathlib: `Real.pi`, `Complex.normSq`, `Space 2`, `MeasureTheory.volume`, almost-everywhere equality, `NNReal`, `Fin`, and `Function.Injective`.

## Local abstractions introduced

- `RectangularWellElectronSetup` preserves independent dimensionful mass, action, side lengths, and energy, plus two quantum numbers and a genuine two-dimensional `L²` state.
- `RectangularWellFigure` preserves the labels and geometry actually visible in the primary raster.
- `DetectionProbeObservation`, `LiesOnProbeLine`, `detectionProbabilityDensity`, and `IsDetectionProbabilityMaximumAlong` give the prose's probe maxima a pointwise physical meaning rather than reducing the observations to unexplained scalar equalities.
- `SatisfiesInfiniteRectangularWellLaws` is local because no matching Physlib two-dimensional infinite-well spectrum or stationary-state API was found. Its equations are the standard general laws and are independent of the measured numbers and requested energy.
- The electron-mass calibration is local because no electron rest-mass constant was found in the searched Physlib API.

## Grounding gaps and redraft requests

- LeanExplore did not find a two-dimensional infinite rectangular-well spectrum, eigenstate, or probe-maximum theorem in Mathlib/Physlib.
- LeanExplore did not find a Physlib electron-mass constant suitable for this calculation.
- The source answer choices appear mismatched with the physical scenario: they are single-`n`, single-`d` symbolic expressions and contain extra powers of `π` relative to the standard formula when `h` denotes ordinary Planck's constant. They cannot express the energy determined by both measured spacings. The recorded C label was preserved as metadata but deliberately not asserted as the physical result. The blueprint/source should be redrafted or the answer choices corrected before a later answer-choice theorem is requested.
- The required project-local `.archon/AGENTS.md` was absent. The available `.archon/prover-modes/physics-formalize.md` and the full task instructions were followed instead.

## Verification

- `archon-lean-lsp` diagnostics: success, with only four expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0584.lean`: exit code 0, with the same four expected warnings.

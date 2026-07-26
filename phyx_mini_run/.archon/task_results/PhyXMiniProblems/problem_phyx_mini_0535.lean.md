# Autoformalization result: `problem_phyx_mini_0535.lean`

## Assumption/target split

### Governing laws

- Each electron is modeled in the common `n = 1` spatial mode of a one-dimensional infinite rigid box spanning the two outermost pictured particles. Since the image has three adjacent gaps, the box length is `3d`.
- The two electrons have opposite spin, so both may occupy that ground spatial mode.
- Each electron's kinetic energy obeys `E₁ = (πℏ)² / (2mL²)` for every positive trial separation.
- Each of the six unordered particle pairs obeys the pairwise Coulomb-energy law `Uᵢⱼ = k qᵢ qⱼ / rᵢⱼ`.
- The total energy is the sum of both electron kinetic energies and all six pair potentials.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- Four collinear particles occur in the order electron--ion--electron--ion.
- The two ions are fixed and have charge `+e`; both electrons have charge `-e`.
- The three adjacent gaps are all marked by double-headed arrows labelled `d`.
- The primary image styles the first and third particles as small blue spheres and the second and fourth as large red spheres, with a vertical guide line at every center.
- Pair distances are `d`, `2d`, or `3d` according to the number of intervening adjacent gaps.
- `Constants.ℏ`, `ChargeUnit.elementaryCharge`, the electron-mass SI calibration, and a free-space Coulomb-constant SI calibration supply the numerical reference data.

### Current target conclusions

- The positive total-energy curve has a minimizer unique by physical length readout.
- Its metre readout is
  `2 π² ℏ² / (21 k m e²)`.
- Its picometre readout is within `0.2 pm` of the displayed `49.9 pm`.
- Recorded answer D is uniquely closest among the four displayed choices.

## Physical model extracted

The image gives six Coulomb pairs. The three unlike-charge adjacent pairs contribute `-3ke²/d`, the outer unlike-charge pair contributes `-ke²/(3d)`, and the two like-charge pairs at distance `2d` contribute `+ke²/d` in total. Hence the electrostatic term is `-7ke²/(3d)`.

The crystal spans `3d`. Two opposite-spin electrons in its common rigid-box ground spatial mode contribute total kinetic energy `π²ℏ²/(9md²)`. Thus the derived curve is

`E(d) = π²ℏ²/(9md²) - 7ke²/(3d)`,

whose positive stationary point is `2π²ℏ²/(21kme²)`. This model reproduces the recorded `49.9 pm` choice at the precision of the source constants/answers.

## Source/law/answer audit

- **Source:** direct inspection of `phyx_data/test_image/535.png` confirms four horizontally collinear centers, alternating small-blue and large-red spheres, one vertical guide at each center, and three equal adjacent spans each labelled `d` with arrowheads at both ends. The source prose, rather than colour alone, identifies the objects as two fixed `+e` ions and two electrons.
- **Law reconstruction:** the literal prompt does not state an electron confinement Hamiltonian. The one-dimensional rigid-box model of length `3d`, common `n = 1` spatial mode for opposite spins, all-six-pairs Coulomb law, and additive energy accounting are therefore explicit modeling assumptions rather than hidden definitions. They are the quantum model consistent with the metadata and recorded numerical answer.
- **Algebra:** the Coulomb coefficients are `-1 + 1/2 - 1/3 - 1 + 1/2 - 1 = -7/3`, while the two box energies total `π²ℏ²/(9md²)`. Differentiating `A/d² - B/d` gives the positive stationary length `2π²ℏ²/(21kme²)`.
- **Answer:** using `ℏ = 1.054571817e-34 J·s`, `mₑ = 9.1093837139e-31 kg`, `k = 8.9875517923e9`, and the Physlib elementary-charge scale `e = 1.602176634e-19 C` gives `d = 49.7406639636 pm`. Its distance from `49.9 pm` is about `0.15934 pm`, below the formalized `0.2 pm` tolerance; it is uniquely closer to D than to A, B, or C. Thus the pictured-law model and recorded answer agree.

## Goal-faithfulness audit

- No scenario, figure, reference-data, positivity, rigid-box-law, Coulomb-law, or energy-accounting field asserts that any separation minimizes energy.
- No premise mentions `49.9 pm`, answer D, `stationarySeparationInMeters`, `IsEnergyMinimizingSeparation`, or `IsUniqueClosestDisplayedSeparation`.
- `stationarySeparationInMeters` is only the analytic expression obtained by balancing the independent inverse-square and inverse-distance coefficients. Defining this candidate does not prove it is positive, realized by a dimensionful length, globally minimizing, unique, numerically close to `49.9 pm`, or closest to D; all of those remain conclusions with `sorry` bodies.
- The numerical answer is compared to an independently modeled physical minimizer. It is not used to define a setup field or governing law.
- Physical primitives are not transparent real aliases: lengths, positions, mass, charge, action, and energy use `Dimensionful`/`DimEnergy`. Reals are confined to named unit readouts and dimensionless/numerical data.

## Declarations and blueprint correspondence

Blueprint label `thm:physics:phyx_mini_0535:target` is represented by:

- `totalEnergyCurve_eq`: derives the scalar total-energy curve from the figure geometry and governing laws.
- `exists_unique_minimizing_separation`: states existence, the analytic length formula, global minimality, and uniqueness by length readout, without answer-choice data.
- `problem_phyx_mini_0535`: final theorem combining the physical minimizer, the analytic formula, the `0.2 pm` numerical bound, and unique selection of recorded answer D.

Supporting declarations include the dimensionful quantity/readout layer, `CrystalParticle`, `ElectronLabel`, `ParticlePair`, `FourParticleCrystalFigure`, `FourParticleCrystalSetup`, the scenario/figure/reference/positivity interfaces, both governing-law structures, and the independent minimum/answer-choice predicates.

## LeanExplore queries and candidates used

Queries were run with `packages: ["Mathlib", "Physlib"]` as required.

- Natural-language `dimensionful physical length charge energy unit readout` found `Dimension`, `Dimension.L𝓭`, `LengthUnit`, `Dimensionful`, `DimEnergy`, `UnitChoices.dimScale`, and `ChargeUnit`/`ChargeUnit.scale`.
- Natural-language `particle in one-dimensional infinite square well ground-state energy` returned finite-ensemble, harmonic-oscillator, free-particle, general quantum-system, and point-particle-potential neighbors, but no infinite-square-well energy spectrum.
- Natural-language `pairwise Coulomb potential energy of point charges` found `Electromagnetism.EMSystem.coulombConstant` and nearby hydrogen/point-particle potential declarations, none of which directly states the finite six-pair scalar energy used here.
- Natural-language `reduced Planck constant electron mass physical constants` found `Constants.ℏ` and its positivity lemmas, but no electron-mass constant.
- Likely-name `IsMinOn` found the exact Mathlib minimum-on-a-set predicate.
- Likely-name query `LengthUnit.picometers ChargeUnit.elementaryCharge DimEnergy Electromagnetism.EMSystem.coulombConstant`, followed by the focused queries `ChargeUnit.elementaryCharge`, `ChargeUnit.coulombs`, `UnitChoices.SI`, and `Electromagnetism.EMSystem`, grounded the unit and electromagnetic APIs used in the file. The exact query `LengthUnit.meters` ranked neighboring metric units rather than `meters`; the fetched `UnitChoices.SI` source explicitly identifies its length field as `LengthUnit.meters`.
- Natural-language `global minimum of a real-valued function on positive real numbers` found `IsMinOn`-based convex/local-to-global neighbors; the focused `IsMinOn` query supplied the predicate itself.
- Natural-language `electron mass kilograms physical constant` and `Bohr radius physical constant` returned no matching electron-mass or Bohr-radius constants.

Source and module details were fetched for the declarations actually used: LeanExplore IDs `394284` (`Dimensionful`), `393156` (`LengthUnit.picometers`), `385585` (`ChargeUnit.elementaryCharge`), `385584` (`ChargeUnit.coulombs`), `385562` (`Electromagnetism.EMSystem`), `385566` (`Electromagnetism.EMSystem.coulombConstant`), `390795` (`Constants.ℏ`), `394468` (`DimEnergy`), `394270` (`UnitChoices.SI`), and `284601` (`IsMinOn`).

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `L𝓭`, `M𝓭`, `C𝓭`, `T𝓭`
- `UnitChoices.SI`
- `LengthUnit.meters`, `LengthUnit.picometers`
- `ChargeUnit.coulombs`, `ChargeUnit.elementaryCharge`
- `DimEnergy`
- `Constants.ℏ`
- `Electromagnetism.EMSystem`, `Electromagnetism.EMSystem.coulombConstant`
- `IsMinOn`

## Local abstractions introduced

- `FourParticleCrystalSetup` preserves independent particle roles, charges, positions, pair distances, box length, component energies, and total energy for every trial separation.
- `ParticlePair` explicitly enumerates all six Coulomb pairs, while `gapCount` preserves the figure-derived `d`, `2d`, and `3d` distances.
- `SatisfiesRigidBoxGroundStateLaw` supplies the missing infinite-square-well ground-state law as a general all-positive-separations physical law.
- `SatisfiesCoulombAndTotalEnergyLaws` supplies pairwise Coulomb energy and additive accounting because the nearby Physlib electromagnetic-potential declarations do not directly express this finite static four-charge energy model.
- `IsUniqueEnergyMinimizingSeparation` uses Mathlib's `IsMinOn` and adds uniqueness only at the physical length-readout level.

These abstractions retain the physical distinctions and do not encode the requested numerical conclusion.

## Grounding gaps and redraft requests

- LeanExplore exposed no infinite-rigid-box spectrum, electron-mass constant, or Bohr-radius constant in the searched Mathlib/Physlib packages, so faithful local law/reference interfaces were used.
- `Electromagnetism.EMSystem.coulombConstant` is an SI-style scalar derived from the system's scalar permittivity rather than a dimensionful Coulomb-constant object. It was used as the available Physlib API while all lengths, charges, and energies remain dimensionful and equations are explicitly SI readouts.
- The supplied blueprint chapter contains the physics marker and target environment but no informal derivation. The rigid-box `3d` model was reconstructed from the primary figure, quantum-phenomena metadata, and the recorded `49.9 pm` result. A later blueprint redraft should state this intended modeling assumption explicitly.
- The requested `.archon/AGENTS.md` file and the advertised `archon` executable were absent, so the available `.archon/prover-modes/physics-formalize.md` role instructions were followed and DAG navigation could not be performed.
- The blueprint environment was not marked `\leanok` because the task's explicit write permissions allow edits only to the assigned Lean file and this result report. The blueprint owner should add `\leanok` to `thm:physics:phyx_mini_0535:target` after review.

## Verification

- `archon-lean-lsp` diagnostics: no errors; exactly three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0535.lean`: succeeds with the same three expected warnings.

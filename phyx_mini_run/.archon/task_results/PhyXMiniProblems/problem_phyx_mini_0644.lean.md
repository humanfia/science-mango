# Autoformalization result: `problem_phyx_mini_0644.lean`

## Assumption/target split

### Governing laws

- `SatisfiesGroundStateIonizationLaw.requiredEnergyIsThresholdGap` states the
  general ground-state ionization relation
  `E_ion = E_threshold - E_ground` in coherent-SI readouts.
- `HasPhysicalElementXParameters` states strict ordering of the three bound
  levels below the continuum and positivity of the independent ionization
  energy observable.
- Neither interface contains `6.5 eV`, `(13 / 2 : ℝ)`, choice `B`, or a
  displayed-answer matching assertion.

### Previous-part results

- None.  The source report has an empty `previous_parts` array, and no
  previous-part lemma is assumed.

### Figure/data readouts

- `MatchesElementXScenario` identifies the species as the fictitious element
  X, the ground state as `n = 1`, and the ionization threshold as the
  zero-energy continuum line.
- `MatchesSuppliedEnergyLevelFigure` records the primary image's four
  horizontal lines; principal-quantum-number labels `n = 1, 2, 3`; physical
  and displayed level readouts `-6.50`, `-3.00`, `-2.00`, and `0.00 eV`;
  their vertical ordering; solid brown bound-level lines; the dashed red
  continuum line; and the `E (eV)` axis text.
- The raster at `phyx_data/test_image/644.png` was inspected directly and
  agrees with these fields.

### Current target conclusions

- `energyInElectronVolts setup.ionizationEnergy = 13 / 2`.
- The physical energy exactly matches displayed choice `B`.
- Choice `B` is the unique displayed answer with that energy.

All three appear only on the conclusion side of
`problem_phyx_mini_0644` (or in general answer-semantics definitions), not in
any theorem premise.

## Goal-faithfulness audit

`ElementXIonizationSetup.ionizationEnergy` is an independent `DimEnergy`
field; it is not defined as a gap or as an answer value.  The figure premise
calibrates only the atomic level energies, and the scenario premise identifies
which existing levels play the ground-state and continuum roles.  The law
premise is uniform in those selected levels and gives only the physical
threshold-minus-ground relation.  Consequently the specialized `6.5 eV`
answer still has to be derived from the scenario, figure calibration, and
governing law.  No premise structure, local definition, or metadata constant
asserts the current numerical conclusion.

`recordedDatasetAnswer := .B` is isolated metadata and is not accepted as a
premise by the theorem.  `AnswerChoice.energyElectronVolts` faithfully records
all four displayed values, including their signs.  The target is neither
`True`, a reflexive equality, nor a definition-unfolding tautology.

## Declarations and blueprint labels

- `problem_phyx_mini_0644` formalizes
  `thm:physics:phyx_mini_0644:target`.
- Supporting declarations without separate blueprint environments:
  `energyInJoules`, `energyInElectronVolts`, `AtomicSpecies`,
  `AtomicEnergyLevel`, `EnergyLevelLineStyle`, `EnergyLevelLineColor`,
  `AtomicEnergyLevelFigure`, `ElementXIonizationSetup`,
  `MatchesElementXScenario`, `MatchesSuppliedEnergyLevelFigure`,
  `HasPhysicalElementXParameters`, `SatisfiesGroundStateIonizationLaw`,
  `AnswerChoice`, `AnswerChoice.energyElectronVolts`,
  `recordedDatasetAnswer`, `MatchesDisplayedIonizationEnergy`, and
  `IsUniqueMatchingIonizationEnergyChoice`.

The assigned Lean source did not exist at task start, so it was created.

## LeanExplore queries and candidates

- Natural-language query: `ionization energy of an atom as continuum
  threshold minus ground-state energy; atomic energy levels in electron
  volts`, with packages `Mathlib` and `Physlib`.
  - Used `DimEnergy` (ID 394468).
  - Used `DimEnergy.electronVolt` (ID 394470).
  - Results such as `CanonicalEnsemble.twoState_energy_fst` and
    `QuantumMechanics.HydrogenAtom.potential_eq` were near misses: they model
    specific ensembles or hydrogen potentials, not a fictitious atom's
    textbook ionization threshold.
- Likely-name query: `ionizationEnergy electronVolt Energy`, with packages
  `Mathlib` and `Physlib`.
  - Again found `DimEnergy` and `DimEnergy.electronVolt`, but no ionization
    energy declaration.
- Source, module, and docstrings were fetched for the two candidates actually
  used.  An LSP local search and standalone compilation snippet additionally
  verified `DimEnergy`, `DimEnergy.electronVolt`, `UnitChoices.SI`, and the
  eV-readout syntax.

## Physlib/Mathlib names grounded

- Physlib `Physlib.Units.WithDim.Energy`:
  - `DimEnergy`, a dimensionful energy with dimension `M L² T⁻²`;
  - `DimEnergy.electronVolt`, the calibrated dimensionful value of one eV;
  - `UnitChoices.SI`, used for coherent-SI evaluation.
- Mathlib supplies `ℝ`, `Option`, `Fintype`, and the ordinary algebraic and
  order vocabulary used in the declarations.

## Local abstractions introduced

- `AtomicEnergyLevel` distinguishes the three bound states from the continuum
  threshold instead of representing physical states by bare scalars.
- `AtomicEnergyLevelFigure` separates literal raster data and scalar eV
  labels from the atom's dimensionful energies.
- `ElementXIonizationSetup` preserves the atomic species, ground-level,
  threshold, dimensionful spectrum, and independent ionization-energy roles.
- `SatisfiesGroundStateIonizationLaw` supplies the smallest faithful local
  governing-law interface missing from Physlib.  It states the generic energy
  gap law, not the specialized numerical answer.
- The answer-choice predicates preserve exact multiple-choice semantics
  without making the recorded answer a hypothesis.

## Grounding gaps and redraft requests

- LeanExplore exposed no Mathlib/Physlib declaration for atomic ionization
  energy or a generic bound-level-to-continuum law, so the local governing-law
  interface above is required.
- The `archon` executable advertised for dependency-graph navigation was not
  on `PATH` (`archon: command not found`), so no DAG ancestors could be
  inspected.
- `.archon/AGENTS.md` was absent.  The available
  `.archon/prover-modes/physics-formalize.md` and `.archon/PROGRESS.md` were
  used as the project-role instructions.
- The existing blueprint environment contains only the autoformalization
  meta-instruction rather than a worked informal derivation.  It was not
  edited or marked `\leanok` because this task's write permissions explicitly
  allow edits only to the assigned Lean file and this task-result file.  A
  blueprint maintainer should attach `\lean{PhyXMiniProblems.ProblemPhyXMini0644.problem_phyx_mini_0644}`
  and `\leanok` after review.

## Verification

- `archon-lean-lsp` diagnostics: success with exactly one expected
  `declaration uses sorry` warning on the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0644.lean`: exit code 0,
  with the same expected warning and no errors.

# Autoformalization result: `problem_phyx_mini_0600.lean`

This is the genuine post-formalization report for Archon iteration 003.  The
review-gate reason was missing post-formalization evidence, not a reported
semantic defect.  I re-read the source report, primary PNG, completed Lean
model, and blueprint chapter, reran the searches recorded below, and checked
the result in the real Lake environment.

## Assumption/target split

### Governing laws

- `SatisfiesAbruptPotentialDropLaws` states the regional energy balance
  `K = E - V`, the nonrelativistic dispersion law `ℏ² k² = 2 m K`, the
  general abrupt-step transmission/reflection flux coefficients, and flux
  conservation.  The fields are unspecialized in energies and wave numbers.
- `HasPhysicalPotentialDropParameters` supplies positive mass, action,
  regional kinetic energies, and wave numbers, plus ordinary event-probability
  bounds.  These conditions select the positive physical branch without
  fixing its value.
- `UsesStandardReducedPlanckConstant` identifies the dimensionful action's SI
  readout with Physlib's positive `Constants.ℏ` value.
- `ModelsEntryAsAbsorptionInducingFission` is a separate idealized capture law:
  transmitted flux is identified with absorption initiating fission.  It is a
  nonnumeric event-identification relation, not a consequence of sharp-step
  scattering.

### Previous-part results

- None.  `reports/phyx_mini/problem_phyx_mini_0600.source.json` has
  `previous_parts: []` and no problem/part dependency.

### Figure/data readouts

- `MatchesNeutronNucleusScenario` records the neutron, rightward incidence,
  interface at `x = 0`, outside potential zero, and inside potential `-V₀`.
- `MatchesProblemEnergyReadouts` records only the supplied incident kinetic
  energy `4 MeV` and well depth `12 MeV`.
- `MatchesSuppliedPotentialDropFigure` records evidence visible in the primary
  `600.png`: `x` and `V(x)` axes, zero outside plateau, lower `-V₀` inside
  plateau, the vertical interface, two-wheeled cart, and rightward arrow.
  Raster coordinates are explicitly dimensionless presentation readouts, not
  calibrated physical coordinates or energies.
- Direct inspection with the image viewer and PNG metadata found dimensions
  `851 × 406`.  The prior draft/chapter topology said `850 × 406`; the Lean
  premise was corrected to the primary-image-supported width `851`.
- `NeutronPotentialDropSetup` keeps mass, reduced Planck action, position,
  signed regional energies, nonnegative wave numbers, figure evidence, and
  the three event probabilities as independent quantities.

### Current target conclusions

- `insideToOutsideWaveNumberRatio` concludes `k_inside / k_outside = 2` by
  deriving the inside kinetic energy `16 MeV` from the two source energies and
  applying the common-mass/common-action dispersion laws.
- `neutronEntryTransmissionProbabilityAtNuclearPotentialDrop` concludes the
  sharp-step entry probability `8/9`, agreement with the displayed `0.8889`,
  and nearest answer choice C.  It makes no absorption claim.
- `neutronAbsorptionProbabilityAtNuclearPotentialDrop` concludes the same
  value and answer semantics for absorption only under the separate capture
  idealization.  This is the formalization target at
  `thm:physics:phyx_mini_0600:target`.

## Goal-faithfulness audit

No current conclusion is present in a hypothesis, structure field, or helper
definition.  In particular:

- the setup stores reflection, transmission, and absorption probabilities
  independently;
- no premise contains `16 MeV`, the wave-number ratio `2`, probability `8/9`,
  rounded value `0.8889`, or answer label C;
- the step-scattering premise contains only the general coefficient
  `4 k_out k_in / (k_out + k_in)^2`, so the source energies, energy balance,
  dispersion, positivity, and algebra are still needed;
- the capture premise equates two physical event probabilities but supplies no
  number and is absent from the unconditional transmission theorem; and
- `displayedAbsorptionProbability` and `recordedDatasetAnswer` encode source
  metadata, but `recordedDatasetAnswer` is not a theorem premise, while
  rounded agreement and nearest-choice status remain theorem conclusions.

Thus the sharp-step model honestly supports entry/transmission probability
`8/9`; certain absorption/fission is exposed as an additional conditional
idealization rather than silently attributed to step scattering.

## Declarations and blueprint labels

- Main target:
  `PhyXMiniProblems.ProblemPhyXMini0600.neutronAbsorptionProbabilityAtNuclearPotentialDrop`
  corresponds to `thm:physics:phyx_mini_0600:target`.
- Intermediate theorem:
  `neutronEntryTransmissionProbabilityAtNuclearPotentialDrop` corresponds to
  `thm:physics:phyx-mini-0600:phyxminiproblems-problemphyxmini0600-neutronentrytransmissionprobabilityatnuclearpotentialdrop`.
- Supporting lemma `insideToOutsideWaveNumberRatio` corresponds to
  `lem:physics:phyx-mini-0600:phyxminiproblems-problemphyxmini0600-insidetooutsidewavenumberratio`.
- Quantity and readout declarations `MassQuantity`, `actionDimension`,
  `ActionQuantity`, `SignedLengthQuantity`, `WaveNumberQuantity`,
  `energyInJoules`, `energyInMegaElectronVolts`, `massInKilograms`,
  `actionInJouleSeconds`, `positionInMeters`, and
  `waveNumberInInverseMeters` correspond to the chapter's same-named
  `def:physics:phyx-mini-0600:phyxminiproblems-problemphyxmini0600-*`
  environments.
- Physical-role and setup declarations `ParticleSpecies`, `PotentialRegion`,
  `ScatteringEvent`, `HorizontalDirection`, `FigureAxis`, `AxisSymbol`,
  `PotentialLevelLabel`, `AbruptPotentialDropFigure`, and
  `NeutronPotentialDropSetup` correspond to their same-named definition
  environments in the declaration topology.
- Premise declarations `MatchesNeutronNucleusScenario`,
  `MatchesProblemEnergyReadouts`, `MatchesSuppliedPotentialDropFigure`,
  `HasPhysicalPotentialDropParameters`, `UsesStandardReducedPlanckConstant`,
  `SatisfiesAbruptPotentialDropLaws`, and
  `ModelsEntryAsAbsorptionInducingFission` correspond to their same-named
  definition environments.
- Answer declarations `AnswerChoice`, `displayedAbsorptionProbability`,
  `recordedDatasetAnswer`, `IsNearestAnswerChoice`, and
  `AgreesWhenRoundedToFourDecimals` likewise correspond to their same-named
  definition environments.

The blueprint was not edited or marked `\leanok`: this task's explicit write
permissions permit only the assigned Lean file and this result file, and
explicitly prohibit editing blueprint chapters.

## LeanExplore queries and candidates actually used

Every query below was run during this post-formalization review with
`packages: ["Mathlib", "Physlib"]`.

- `one dimensional quantum abrupt potential step transmission reflection
  probability flux coefficient` returned
  `QuantumMechanics.SpaceDQuantumSystem.potentialCLM` and related generic
  potential operators, reflectionless-potential declarations, and unrelated
  category-theory reflection steps.  It returned no abrupt potential-step
  flux theorem.
- `Schrodinger equation potential step scattering wave number transmission
  coefficient` returned the generic `ClassicalMechanics.WaveEquation`, a
  tight-binding Schrödinger theorem, electromagnetic waves, and
  `QuantumMechanics.SpaceDQuantumSystem.potentialCLM`, but no compatible
  scattering coefficient.
- `Dimensionful WithDim energy mass length inverse length reduced Planck
  constant electron volt` returned `Dimensionful`, `DimEnergy`,
  `DimEnergy.electronVolt`, `Dimension`, `Dimension.L𝓭`, and `Constants.ℏ`.
- `WithDim physical dimension tagged type` returned `WithDim` and its actual
  dimension-tag API.
- `Dimension.M𝓭 Dimension.T𝓭 mass time physical dimensions` returned
  `Dimension.M𝓭`, `Dimension.L𝓭`, and `Dimension.T𝓭`.
- `UnitChoices.SI coherent SI unit choices` returned `UnitChoices.SI` and its
  base-unit projections.

Source, module, and docstring were fetched for the candidates actually used:
`Dimensionful` (`Physlib.Units.Basic`), `WithDim`
(`Physlib.Units.WithDim.Basic`), `DimEnergy` and
`DimEnergy.electronVolt` (`Physlib.Units.WithDim.Energy`), `Constants.ℏ`
(`Physlib.QuantumMechanics.PlanckConstant`), `UnitChoices.SI`
(`Physlib.Units.Basic`), and the three base dimensions
(`Physlib.Units.Dimension`).  The fetched source confirms that `DimEnergy` is
dimensionful, `electronVolt` is calibrated to joules, `SI` selects metres,
seconds, kilograms, coulombs, and kelvin, and `Constants.ℏ` is a positive SI
J·s readout.

The source of the main near miss,
`QuantumMechanics.SpaceDQuantumSystem.potentialCLM`, was also fetched.  It is a
continuous linear multiplication operator on Schwartz space; it does not
encode two constant regions, boundary matching, incident/reflected waves, or
probability flux, so it was not forced into this model.

## Physlib/Mathlib names grounded

- Physlib names used and grounded: `Dimensionful`, `WithDim`, `Dimension`,
  `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `DimEnergy`,
  `DimEnergy.electronVolt`, `UnitChoices.SI`, and `Constants.ℏ`.
- Mathlib supplies `NNReal`, real powers/division/absolute value, and the
  finite/decidable infrastructure used by the local inductive types.  The
  actual imports and elaborated signatures were additionally verified by Lean
  diagnostics and `lake env lean`.

## Local abstractions introduced

- `MassQuantity`, `ActionQuantity`, `SignedLengthQuantity`, and
  `WaveNumberQuantity` use Physlib's unit-independent
  `Dimensionful (WithDim ...)` representation.  They are not transparent
  scalar aliases; only named SI/unit projections return real readouts.
- `AbruptPotentialDropFigure` plus small role-label inductives preserve the
  distinctions among regions, events, directions, axes, and the `-V₀` label.
- `SatisfiesAbruptPotentialDropLaws` is the smallest local interface needed in
  place of missing abrupt-step infrastructure.  Its laws are standard and
  unspecialized rather than restatements of the numeric goal.
- `ModelsEntryAsAbsorptionInducingFission` preserves the scientifically
  essential distinction between entry and absorption while expressing the
  source's intended idealized interpretation conditionally.

## Grounding gaps and redraft requests

- Mathlib/Physlib provides no compatible ready-made one-dimensional abrupt
  potential-step scattering theorem or probability-flux coefficient.  The
  faithful general local law interface fills this gap.
- The source supplies no nuclear-capture law establishing that every neutron
  crossing the boundary is absorbed and triggers fission.  The Lean statement
  therefore keeps unconditional transmission separate from conditional
  absorption.
- The chapter's generated declaration-topology prose still says `850 × 406`,
  whereas the primary PNG is `851 × 406`.  A later blueprint-owning agent
  should synchronize that description; this agent was not authorized to edit
  the chapter.
- The requested `.archon/AGENTS.md` is absent.  I followed the user-supplied
  role instructions, `.archon/PROGRESS.md`, and
  `.archon/prover-modes/physics-formalize.md`.
- Although the runtime note says `archon` is on `PATH`, it is unavailable in
  this environment (`archon: command not found`).  The authoritative source
  report independently confirms there are no previous parts.

## Verification

- `archon-lean-lsp` diagnostics after the width correction: exactly three
  expected `declaration uses sorry` warnings, at the supporting lemma and two
  target theorems, with no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0600.lean`: exit code 0,
  with the same three expected `sorry` warnings and no errors.

# Iteration 017 prover result

## Status

All three proof obligations in
`PhyXMiniProblems/problem_phyx_mini_0600.lean` are closed without changing
any declaration header, hypothesis, or conclusion.  No redraft is needed.

## Proofs completed

- `insideToOutsideWaveNumberRatio`: used the shared MeV conversion factor to
  derive that the `12 MeV` well depth is three times the `4 MeV` outside
  kinetic energy.  The regional energy-balance laws then give
  `K_inside = 4 K_outside`.  Cancelling the nonzero squared action from the
  two dispersion laws gives `k_inside² = 4 k_outside²`; positivity of both
  wave numbers selects `k_inside = 2 k_outside`, hence the required ratio.
- `neutronEntryTransmissionProbabilityAtNuclearPotentialDrop`: substituted
  the proved positive-branch ratio into the general abrupt-step flux
  coefficient and simplified it to `8/9`.  Exact rational normalization
  proves agreement with the displayed `0.8889` at four decimals and checks
  all four constructors to prove that C is nearest.
- `neutronAbsorptionProbabilityAtNuclearPotentialDrop`: rewrote absorption
  to transmitted flux using only the separate
  `ModelsEntryAsAbsorptionInducingFission` premise, then applied the
  transmission theorem.  The capture premise is not used in either
  transmission result.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0600.lean`: exit code 0,
  with no errors or warnings.
- `lake build`: exit code 0.
- `git diff --check -- PhyXMiniProblems/problem_phyx_mini_0600.lean`: exit
  code 0.
- Source scan found no `sorry`, `admit`, `axiom`, or `sorryAx`.
- No axioms, escape hatches, metaprogramming, or declaration shadowing were
  introduced.

## Blueprint status

The supporting ratio lemma, unconditional transmission theorem, and
conditional absorption target are proof-complete and ready to be marked
`\leanok`.  I did not edit
`blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0600.tex` because
this prover task explicitly restricts writes to the assigned Lean file and
this task-result file and separately prohibits blueprint edits.

## Workflow note

The requested `.archon/AGENTS.md` is absent from this checkout, as
`.archon/PROGRESS.md` also records.  I used the user-supplied role
instructions, `.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, the
physics blueprint chapter, the iteration-017 plan, the source report, and the
file-specific `USER:` comment.

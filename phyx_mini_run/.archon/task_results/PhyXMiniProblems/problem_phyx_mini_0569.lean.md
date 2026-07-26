# Autoformalization result: `problem_phyx_mini_0569.lean`

Archon iteration 003 independently re-audited the current declaration model
against the source report, the primary raster, the blueprint, fresh
LeanExplore results, and the real Lean environment. The review-gate reason was
evidence-only: it did not identify a semantic defect in the revised Lean
model. No Lean redraft was required, and the existing faithful declarations
and their two required `by sorry` bodies were retained.

The chapter contains `% archon:physics`, so the `physics-formalize` discipline
applies.

## Assumption/target split

### Governing laws

- `SatisfiesRelativisticBackscatterLaws.initialElectronAtRest` sets both
  components of the initial electron momentum to zero, and
  `initialElectronEnergyIsRestEnergy` identifies its initial total energy with
  its rest energy.
- `momentumConservation` conserves both components of the dimensionful plane
  momentum.
- `energyConservation` conserves total energy.
- `incidentPhotonEnergyMomentum` and `scatteredPhotonEnergyMomentum` state the
  massless relations `E = pc` for the incoming and outgoing photon.
- `recoilingElectronEnergyMomentum` states
  `E_e^2 = (m_e c^2)^2 + (p_e c)^2`.
- `recoilingElectronMomentumVelocity` states the general outgoing-electron
  relation `v_e = p_e c^2 / E_e`.
- `HasPhysicalBackscatterParameters` supplies positivity and subluminality.
  It supplies no numerical recoil value.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesProblemData` records the stated incident photon energy `100 keV`,
  the standard electron rest-energy calibration `511 keV`, and that the
  initial electron is free. It does not constrain the outgoing speed.
- `MatchesPrimaryBackscatterFigure` records the two before/after panels, the
  printed `x`/`y` axes, the photon/electron labels, the initial electron at the
  axes intersection with no motion arrow, the incident photon along `+x`, the
  scattered photon along `-x`, and the electron recoil along `+x`. Its signed
  component equations preserve this one-dimensional geometry in the
  dimensionful momentum model.
- The `1380 x 394` primary PNG was inspected directly during iteration 003.
  Its left panel shows a photon arrow in `+x` toward an electron at the axes
  intersection. Its right panel shows the photon arrow in `-x` and the
  electron recoil arrow in `+x`. The raster supplies no numerical speed.
- `displayedSpeedFractionOfC` transcribes all four displayed coefficients;
  `recordedDatasetAnswer` preserves the source dataset's answer label as
  metadata, not as a theorem premise.

### Current target conclusions

- `electronRecoilSpeedFraction_from_conservation` derives, rather than
  assumes, the general head-on-backscatter relation
  `v/c = 2 E (E + M) / (M^2 + 2 M E + 2 E^2)`.
- `electronRecoilVelocity_is_choice_C` concludes the instance-specific exact
  ratio `v/c = 122200 / 383321`, nearest-hundredth agreement with `0.32`,
  closeness of choice C, and uniqueness of C as the closest displayed choice.

## Goal-faithfulness audit

`PhotonElectronBackscatterSetup.electronRecoilSpeed` is an independent
`DimSpeed` field. It is related to energy and momentum only through the
general momentum--velocity governing law. Neither `122200 / 383321`, the
rounded value `0.32`, nor the assertion that C is closest occurs in
`MatchesProblemData`, `MatchesPrimaryBackscatterFigure`,
`HasPhysicalBackscatterParameters`, or
`SatisfiesRelativisticBackscatterLaws`. The specialized exact ratio occurs
only in the target theorem, while the general symbolic ratio occurs only in a
lemma conclusion.

The answer table and `recordedDatasetAnswer := .C` are source-presentation
metadata. Neither is a hypothesis to the general conservation lemma or target
theorem, and the setup's speed is not defined from either. Thus no current
target conclusion is smuggled into a premise structure or made true by
unfolding a local definition.

Independent arithmetic audit: substituting `E = 100` and `M = 511` in the
general formula gives numerator `2 * 100 * 611 = 122200` and denominator
`511^2 + 2 * 511 * 100 + 2 * 100^2 = 383321`, hence approximately
`0.318792865510`, which rounds to the displayed `0.32`.

## Declarations and blueprint correspondence

- `PlaneMomentum`, `DiagramAxis`, `DiagramAxis.toFin`, `energyInJoules`,
  `energyInKiloElectronVolts`, `momentumComponentInSI`,
  `momentumMagnitudeInSI`, `speedInMetersPerSecond`, and
  `speedOfLightInMetersPerSecond` correspond to the same-named definition
  environments in the chapter's declaration topology.
- `PhotonState`, `FigurePanel`, `ParticleLabel`, `HorizontalMotion`,
  `PhotonElectronBackscatterFigure`, and
  `PhotonElectronBackscatterSetup` correspond to the chapter's physical-state
  and primary-figure definition environments.
- `MatchesProblemData`, `MatchesPrimaryBackscatterFigure`,
  `HasPhysicalBackscatterParameters`, and
  `SatisfiesRelativisticBackscatterLaws` correspond to the chapter's explicit
  data/figure/physical/law premise environments.
- `electronRecoilSpeedFractionOfC` corresponds to
  `def:physics:phyx-mini-0569:phyxminiproblems-problemphyxmini0569-electronrecoilspeedfractionofc`.
- `electronRecoilSpeedFraction_from_conservation` corresponds to
  `lem:physics:phyx-mini-0569:phyxminiproblems-problemphyxmini0569-electronrecoilspeedfraction-from-conservation`.
- `AnswerChoice`, `displayedSpeedFractionOfC`, `recordedDatasetAnswer`,
  `RoundsToNearestHundredth`, and `IsClosestAnswerChoice` correspond to their
  same-named answer-model environments in the declaration topology.
- `electronRecoilVelocity_is_choice_C` corresponds to target label
  `thm:physics:phyx_mini_0569:target`.

For the exact definition-label mapping, let
`P = def:physics:phyx-mini-0569:phyxminiproblems-problemphyxmini0569-`.
The chapter maps declarations to labels as follows:

- `PlaneMomentum` / `Pplanemomentum`; `DiagramAxis` / `Pdiagramaxis`;
  `DiagramAxis.toFin` / `Pdiagramaxis-tofin`.
- `energyInJoules` / `Penergyinjoules`;
  `energyInKiloElectronVolts` / `Penergyinkiloelectronvolts`;
  `momentumComponentInSI` / `Pmomentumcomponentinsi`;
  `momentumMagnitudeInSI` / `Pmomentummagnitudeinsi`.
- `speedInMetersPerSecond` / `Pspeedinmeterspersecond`;
  `speedOfLightInMetersPerSecond` / `Pspeedoflightinmeterspersecond`.
- `PhotonState` / `Pphotonstate`; `FigurePanel` / `Pfigurepanel`;
  `ParticleLabel` / `Pparticlelabel`; `HorizontalMotion` /
  `Phorizontalmotion`.
- `PhotonElectronBackscatterFigure` /
  `Pphotonelectronbackscatterfigure`;
  `PhotonElectronBackscatterSetup` / `Pphotonelectronbackscattersetup`.
- `MatchesProblemData` / `Pmatchesproblemdata`;
  `MatchesPrimaryBackscatterFigure` / `Pmatchesprimarybackscatterfigure`;
  `HasPhysicalBackscatterParameters` / `Phasphysicalbackscatterparameters`;
  `SatisfiesRelativisticBackscatterLaws` /
  `Psatisfiesrelativisticbackscatterlaws`.
- `electronRecoilSpeedFractionOfC` / `Pelectronrecoilspeedfractionofc`.
- `AnswerChoice` / `Panswerchoice`; `displayedSpeedFractionOfC` /
  `Pdisplayedspeedfractionofc`; `recordedDatasetAnswer` /
  `Precordeddatasetanswer`; `RoundsToNearestHundredth` /
  `Proundstonearesthundredth`; `IsClosestAnswerChoice` /
  `Pisclosestanswerchoice`.

Here `P...` denotes literal concatenation with the displayed common prefix.
The conservation lemma and target theorem use the two full labels already
listed above.

## LeanExplore queries and candidates actually used

All four iteration-003 searches used
`packages: ["Mathlib", "Physlib"]`:

- Natural-language query:
  `relativistic photon electron scattering energy momentum conservation`.
  It returned `ClassicalMechanics.FreeParticle.linearMomentum_conserved` and
  `ClassicalMechanics.FreeParticle.linearMomentum_conserved_of_velocity_const`
  as classical near misses, plus dimensional primitives. It returned no
  relativistic photon--electron collision API.
- Likely-name query: `DimEnergy electronVolt`.
- Likely-name query: `DimSpeed speedOfLight`.
- Mixed concept/name query: `Dimensionful Momentum spatial vector`.

Sources and modules were fetched for every candidate retained in the Lean
model:

- `DimEnergy` (id `394468`) and `DimEnergy.electronVolt` (id `394470`) from
  `Physlib.Units.WithDim.Energy`.
- `DimSpeed` (id `394481`) and `DimSpeed.speedOfLight` (id `394486`) from
  `Physlib.Units.WithDim.Speed`.
- `Momentum` (id `394473`) from `Physlib.Units.WithDim.Momentum`.
- `Dimensionful` (id `394284`) from `Physlib.Units.Basic`.

The fetched sources confirm that `DimEnergy` has dimension
`M L^2 T^-2`, `DimSpeed` has dimension `L T^-1` with nonnegative scalar
values, one electron-volt is calibrated as `1.602176634e-19 J`, and the speed
of light is calibrated as exactly `299792458 m/s`. The `Momentum` source
explicitly says it is spatial momentum rather than four-momentum.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful`, `UnitChoices.SI`, `DimEnergy`,
  `DimEnergy.electronVolt`, `Momentum`, `DimSpeed`, and
  `DimSpeed.speedOfLight`.
- Mathlib: `Real.sqrt` for the Euclidean norm of the two SI momentum
  components.
- Project-local LSP search independently located `DimEnergy` and `Momentum` in
  the imported Physlib modules. LSP elaboration and standalone compilation
  also resolve the namespaced speed-of-light declaration used in the file.

## Local abstractions introduced

- `PlaneMomentum := Dimensionful (Momentum 2)` specializes Physlib's genuine
  dimensionful spatial momentum to the two axes of the supplied diagram. It is
  not a scalar alias.
- `PhotonState` groups independent dimensionful photon energy and momentum.
- `FigurePanel`, `DiagramAxis`, `ParticleLabel`, `HorizontalMotion`, and
  `PhotonElectronBackscatterFigure` preserve the named panels, labels, axes,
  and qualitative arrow directions visible in the raster.
- `PhotonElectronBackscatterSetup` preserves independent incoming/outgoing
  photon states, initial/outgoing electron energy-momenta, rest energy, and
  recoil speed.
- `SatisfiesRelativisticBackscatterLaws` is the smallest faithful local law
  interface needed because no compatible collision-level Physlib API was
  found. It states conservation, dispersion, and velocity laws in general
  form; it does not state the requested specialized answer.
- The answer-choice and rounding predicates preserve the source's discrete
  presentation separately from the physical state.

## Grounding gaps and redraft requests

- LeanExplore found no ready-made relativistic photon--electron scattering
  state, photon dispersion law, or collision-level four-momentum conservation
  API. The returned classical free-particle conservation lemmas do not model
  this collision and were not used. The local law structure is therefore
  retained.
- No semantic redraft is requested. The source, raster, governing laws,
  symbolic result, and recorded answer agree.
- `.archon/AGENTS.md` is absent from the workspace. The explicit task prompt
  and `.archon/prover-modes/physics-formalize.md` supplied the applicable role
  discipline.
- The assigned Lean file contains no `/- USER: ... -/` comments.
- The `archon` executable is not present on `PATH`, so the optional DAG query
  could not be run.
- The blueprint chapter exists and is marked `% archon:physics`. It was not
  edited with `\\leanok` because the explicit write permissions permit edits
  only to the assigned Lean file and this task-result file. The coordinator
  should mark the already-formalized environments.

## Source/law/answer audit

- Source: `100 keV`, an electron initially at rest, choices `0.55c`, `0.95c`,
  `0.32c`, and `10.2c`, and recorded answer C were confirmed in the source
  report.
- Figure: the inspected raster supports head-on one-dimensional photon
  backscatter and electron recoil in `+x`; it provides no answer magnitude.
- Laws: plane momentum and total energy conservation, both photon `E = pc`
  laws, the electron relativistic dispersion relation, and `v = p c^2 / E`
  are explicit assumptions.
- Answer: the general laws derive the exact symbolic ratio, and the instance
  data specialize it to approximately `0.3188`, consistent with choice C.

## Verification

- `archon-lean-lsp` diagnostics on the assigned file reported exactly two
  expected `declaration uses sorry` warnings, at
  `electronRecoilSpeedFraction_from_conservation` and
  `electronRecoilVelocity_is_choice_C`, with no errors or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0569.lean` exited with
  code `0` and reported the same two expected warnings and no errors.

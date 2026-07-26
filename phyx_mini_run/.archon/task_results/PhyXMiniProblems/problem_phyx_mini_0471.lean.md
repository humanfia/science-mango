# Autoformalization result: `problem_phyx_mini_0471.lean`

## Retry-gate resolution

The exact final-review reason is that no genuine post-formalization task result
existed for retry target 0471: the generic preflight log predates the revised
Lean model and does not establish the searches, grounded declarations, local
abstractions, gaps, or source/law/answer split actually used. This report is a
fresh audit of the current Lean file against the source report, blueprint, and
primary image. The review reason is evidence-only; the audit found no semantic
defect requiring a change to the current physical statement.

The primary image was inspected directly at `phyx_data/test_image/471.png`.
It confirms that `ab` and `cd` are vertical upward arrows, `ac` and `bd` are
horizontal rightward arrows, and that the displayed pressure and volume
coordinates are exactly those recorded in the Lean premise. This corrects the
auxiliary generated caption, whose prose reverses the segment orientations.

## Assumption/target split

### Governing laws

- `MatchesClosedSystemScenario` records a fixed closed system with negligible
  kinetic- and potential-energy changes.
- `SatisfiesQuasistaticBoundaryWorkLaw` states the general boundary-work laws:
  isochoric legs do zero work and isobaric legs do
  `p * (V_final - V_initial)` work by the system, in coherent SI readouts.
- `SatisfiesPathWorkAdditivity` states that work on each two-leg route is the
  sum of the works on its displayed legs.
- `SatisfiesClosedSystemFirstLaw` states
  `Q = U_final - U_initial + W_by` uniformly for every displayed leg and both
  complete paths.
- `HasPhysicalPressureVolumeCoordinates` records positivity of all plotted
  pressures and volumes.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesPrimaryPressureVolumeFigure` records the image's horizontal `V` axis
  in cubic metres, vertical `p` axis in pascals, origin label `O`, state labels
  `a`, `b`, `c`, `d`, and the four directed arrows.
- It records vertical isochoric legs `a → b` and `c → d`, horizontal
  isobaric legs `a → c` and `b → d`, and the coordinates
  `p_a = p_c = 3.0 × 10^4 Pa`, `p_b = p_d = 8.0 × 10^4 Pa`,
  `V_a = V_b = 2.0 × 10^-3 m^3`, and
  `V_c = V_d = 5.0 × 10^-3 m^3`.
- `MatchesGivenHeatReadouts` contains exactly the prose data
  `Q_ab = 150 J` and `Q_bd = 600 J`.
- `AnswerChoice.displayedHeatInJoules` and `recordedDatasetAnswer` preserve the
  four printed choices and recorded label B as metadata, not theorem premises.

### Current target conclusions

- `problem_phyx_mini_0471` concludes that total heat added on route
  `a → c → d` is exactly `600 J`.
- It also concludes `MatchesDisplayedHeat setup .B`, selecting printed answer
  B from the derived physical result.

## Goal-faithfulness audit

`RectangularPVProcessSetup.heatAddedAlong .acd` is an independent dimensionful
energy observable. It is not defined from `600`, answer B, the work law, or the
first law, and no premise states its value. The given-data structure mentions
only the two source heat readouts. The work and first-law interfaces are
uniform laws over all legs and paths, so deriving the target requires combining
those laws with the image coordinates and the two given heats. The numeric
value associated with answer B occurs only in answer metadata and in the
conclusion-side predicate `MatchesDisplayedHeat`; neither appears as a theorem
hypothesis. Thus the current target was not smuggled into a premise structure,
law field, or unfolding-only local definition.

The source/law/answer calculation represented by the statement is:
`W_ab = 0`, hence `ΔU_ab = 150 J`; `W_bd = 8.0×10^4 * 3.0×10^-3 = 240 J`,
hence `ΔU_bd = 360 J`; therefore `ΔU_ad = 510 J`. Along `acd`,
`W_acd = 3.0×10^4 * 3.0×10^-3 = 90 J`, so the first law yields
`Q_acd = 510 + 90 = 600 J`.

## Declarations created and blueprint labels

- Dimensionful quantities/readouts: `VolumeQuantity`, `PressureQuantity`,
  `EnergyQuantity`, `volumeInCubicMetres`, `pressureInPascals`, and
  `energyInJoules`.
- State/process vocabulary: `StateLabel`, `ProcessLeg`, `ProcessPath`, their
  endpoint/leg maps, `ProcessKind`, and `SegmentOrientation`.
- Figure vocabulary: `FigureAxis`, `AxisQuantity`, `AxisDisplayUnit`,
  `AxisSymbol`, and `PressureVolumeFigure`.
- Physical model: `ThermodynamicSystemBoundary` and
  `RectangularPVProcessSetup`.
- Premise interfaces: `MatchesClosedSystemScenario`,
  `MatchesPrimaryPressureVolumeFigure`, `MatchesGivenHeatReadouts`,
  `HasPhysicalPressureVolumeCoordinates`,
  `SatisfiesQuasistaticBoundaryWorkLaw`, `SatisfiesPathWorkAdditivity`, and
  `SatisfiesClosedSystemFirstLaw`.
- Answer vocabulary: `AnswerChoice`, `AnswerChoice.displayedHeatInJoules`,
  `recordedDatasetAnswer`, and `MatchesDisplayedHeat`.
- `PhyXMiniProblems.ProblemPhyXMini0471.problem_phyx_mini_0471` corresponds to
  blueprint label `thm:physics:phyx_mini_0471:target`. The chapter already has
  the correct `\lean{...}` link. Its statement is ready for `\leanok`, but the
  blueprint was not edited because this lane's explicit permissions make it
  read-only and reserve marker synchronization for a later phase.

## LeanExplore queries and candidates actually used

All four searches were run after reading the revised file, with package filter
`["Mathlib", "Physlib"]`.

- Natural-language query `closed-system first law thermodynamics heat internal
  energy work pressure volume process path` returned, among others,
  `NVEHamiltonian.pressure`, `IdealGas.ideal_gas_law`,
  `MicroHamiltonian.internalU`, `DimPressure`, and adiabatic/statistical
  mechanics declarations. No reusable closed-system first-law or process-path
  declaration was present; `DimPressure` was retained.
- Natural-language query `quasistatic pressure volume boundary work isobaric
  isochoric thermodynamic process` returned pressure-unit declarations,
  `IdealGas.ideal_gas_law`, an adiabatic relation, and an unrelated manifold
  boundary. It exposed no thermodynamic p--V boundary-work theorem.
- Likely-name query `DimEnergy DimPressure Dimensionful UnitChoices.SI joule
  pascal` returned and grounded `Dimensionful` (id 394284), `UnitChoices.SI`
  (394270), `DimEnergy` (394468), `DimEnergy.joule` (394469), `DimPressure`
  (394474), and `DimPressure.pascal` (394475).
- Likely-name/concept query `physical volume dimension length cubed DimVolume
  WithDim L𝓭` returned and grounded `Dimension.L𝓭` (394324) and `WithDim`
  (394425); it returned no dedicated `DimVolume` alias.

LeanExplore source, module, and docstring data were fetched only for those eight
retained declarations. The returned sources confirm the exact types and unit
constructors used in the Lean file.

## PhysLean/Mathlib names grounded

- `Physlib.Units.WithDim.Energy`: `DimEnergy`, `DimEnergy.joule`.
- `Physlib.Units.WithDim.Pressure`: `DimPressure`, `DimPressure.pascal`.
- Physlib unit infrastructure: `Dimensionful` and `UnitChoices.SI` from
  `Physlib.Units.Basic`, `WithDim` from `Physlib.Units.WithDim.Basic`, and
  `Dimension.L𝓭` from `Physlib.Units.Dimension`.
- Mathlib supplies `ℝ`, strings, booleans, inductive/structure support, and
  real arithmetic for named coherent-SI readouts and displayed answer values.

## Local abstractions introduced

- `VolumeQuantity := Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)` fills the
  missing volume alias while preserving dimension `L³`; it is not a scalar
  placeholder.
- `StateLabel`, `ProcessLeg`, and `ProcessPath` preserve the figure labels and
  the two directed routes from `a` to `d`.
- `PressureVolumeFigure` preserves axes, display units, printed symbols,
  origin/state labels, orientations, and arrow directions without inventing a
  nonexistent Physlib diagram API.
- `RectangularPVProcessSetup` keeps pressure, volume, internal energy, heat,
  and work as independent dimensionful quantities with the appropriate
  state-, leg-, or path-dependence.
- The three `Satisfies...` interfaces are the smallest local abstractions for
  boundary work, path-work additivity, and the closed-system first law needed
  by the exercise. Their fields are general laws and contain no requested heat
  value.

## Grounding gaps and redraft requests

- LeanExplore exposed no dedicated dimensionful volume alias, thermodynamic
  process/path object, closed-system first-law theorem, or quasistatic p--V
  boundary-work theorem. The dimension-tagged volume and explicit local law
  interfaces fill these gaps without erasing physical meaning.
- The requested live `.archon/AGENTS.md` is absent. The matching archived
  project role file and the complete live
  `.archon/prover-modes/physics-formalize.md` were read; both confirm that the
  prover owns only its assigned Lean file and result, while blueprint markers
  are synchronized outside this lane.
- The runtime note says `archon` is on `PATH`, but `command -v archon` and both
  target-node DAG commands failed with `command not found`. This is not a
  modeling blocker because the chapter supplies the declaration topology and
  the target has no cross-chapter theorem dependencies.
- No Lean redraft is requested. A marker-sync phase should add the target
  environment's `\leanok` under its blueprint-write authority.

## Verification

- The file imports `Mathlib`, `Physlib.Units.WithDim.Energy`, and
  `Physlib.Units.WithDim.Pressure` directly.
- Lean LSP diagnostics report exactly one expected warning,
  `declaration uses sorry`, on `problem_phyx_mini_0471`, with no failed
  dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0471.lean` exits 0 and
  reports the same single expected warning.
- The only escape hatch in the assigned Lean file is the required
  autoformalization `sorry` body of the target theorem; there is no `axiom`,
  `admit`, or `native_decide`.

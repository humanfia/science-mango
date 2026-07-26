## Assumption/target split

### Governing laws

- `SatisfiesRelativisticReactionLaws.relativisticEnergyMomentum` states the
  generic massive-particle dispersion relation
  `E^2 = (m c^2)^2 + (p c)^2`, with total energy read as `m c^2 + K`.
- `SatisfiesRelativisticReactionLaws.totalEnergyConservation` conserves total
  relativistic energy between `K^- + p` and `Lambda^0 + pi^0`.
- `SatisfiesRelativisticReactionLaws.planeMomentumConservation` conserves both
  displayed spatial-momentum components.

### Previous-part results

- None.  The problem is self-contained.

### Figure/data readouts

- `MatchesReactionProblemData` records the four rest-mass readouts
  `493.7`, `938.3`, `1115.7`, and `135.0 MeV/c^2`, the supplied kinetic
  energies `152.4 MeV` and `254.8 MeV`, and the fact that the proton is at
  rest.  It does not constrain the lambda kinetic energy.
- `MatchesPrimaryReactionFigure` records panels (a) and (b), both `x` and `y`
  axes, the four particle labels, the kaon left of the proton, and the three
  arrow directions.  It also records the image-primary geometry: the kaon is
  along `+x`, the pion is upper-right at acute angle `theta` from `+x`, and
  the lambda is lower-right at acute angle `phi` from `+x`.
- `HasPhysicalReactionParameters` records positive rest masses and
  nonnegative kinetic-energy and momentum-magnitude readouts.

### Current target conclusions

- The lambda kinetic-energy readout is exactly `789 / 10 MeV`, i.e.
  `78.9 MeV`.
- That value is the kinetic energy printed for recorded answer choice D.

## Goal-faithfulness audit

The unknown lambda kinetic energy is an independent `DimEnergy` field of
`ParticleState`.  No setup field, data predicate, figure predicate, physical
parameter predicate, or governing-law field assigns it `78.9 MeV` or equates
it to an answer choice.  Energy conservation relates all four independent
particle energies in the usual way, and the target number is obtained only
after inserting the supplied masses and the two known kinetic energies.

The helper `totalRelativisticEnergyInJoules` is the generic definition
`m c^2 + K`, not the requested result.  The displayed-answer table contains
the source's choices, but no premise selects a row or states agreement with
that table.  Thus neither unfolding a setup definition nor projecting a
premise closes the substantive target.

The iteration-001 gate rejection was evidence-only: it reported that no
post-formalization task result existed.  This report is generated after
inspecting the completed Lean model, source report, and primary raster, and
records the searches and declarations actually used by that model.

## Declarations created

- Physical/readout layer: `RestMassQuantity`, `PlaneMomentum`,
  `restMassInKilograms`, `energyInJoules`,
  `energyInMegaElectronVolts`, `speedOfLightInMetersPerSecond`,
  `restEnergyEquivalentInJoules`,
  `restMassInMegaElectronVoltsPerC2`, `momentumComponentInSI`, and
  `momentumMagnitudeInSI`.
- Reaction/figure layer: `DiagramAxis`, `ParticleLabel`, `ReactionSide`,
  `particleSide`, `FigurePanel`, `PlanarDirection`,
  `KaonProtonReactionFigure`, `ParticleState`, and
  `KaonProtonReactionSetup`.
- Assumption layer: `MatchesReactionProblemData`,
  `MatchesPrimaryReactionFigure`, `HasPhysicalReactionParameters`, and
  `SatisfiesRelativisticReactionLaws`.
- Answer layer: `AnswerChoice`, `displayedLambdaKineticEnergyMeV`, and
  `recordedAnswerChoice`.
- Target theorem: `problem_phyx_mini_0554`, corresponding to blueprint label
  `thm:physics:phyx_mini_0554:target`.

## LeanExplore queries and candidates used

- Natural-language query: `relativistic particle four-momentum energy
  conservation collision rest mass kinetic energy`.  The search returned
  classical free-particle energy/momentum declarations and unit examples, but
  no collision-ready relativistic four-momentum/conservation interface.
- Likely-name query: `FourMomentum energy momentum conservation`.  No
  `FourMomentum` collision API was returned.
- Units query: `physical dimensions units energy mass momentum`.  Relevant
  candidates included `Dimension` and `Momentum`.
- Exact-name queries: `DimEnergy electronVolt`, `Momentum`, and
  `DimSpeed.speedOfLight`.
- Mass/unit-system checks: `DimMass`, `WithDim M𝓭 mass dimension`,
  `Dimensionful`, and `UnitChoices.SI`.  No dedicated `DimMass` quantity was
  returned; the results did ground the general dimension infrastructure.
- Source and module data were fetched for the candidates actually used:
  `Dimensionful` (ID 394284), `Dimension` (ID 394292), `DimEnergy`
  (ID 394468), `DimEnergy.electronVolt` (ID 394470), `Momentum` (ID 394473),
  `DimSpeed.speedOfLight` (ID 394486), and `UnitChoices.SI` (ID 394270).

All searches used package filters `Mathlib` and `Physlib` as requested.

## Physlib/Mathlib names grounded

- `DimEnergy` and `DimEnergy.electronVolt` from
  `Physlib.Units.WithDim.Energy`.
- `Momentum` from `Physlib.Units.WithDim.Momentum`; its fetched source
  confirms that it is spatial momentum, so `Dimensionful (Momentum 2)` is
  appropriate for the two-dimensional raster.
- `DimSpeed.speedOfLight` from `Physlib.Units.WithDim.Speed`.
- `Dimensionful`, `WithDim`, `M𝓭`, `NNReal`, `UnitChoices.SI`, `Real.sqrt`,
  `Real.sin`, `Real.cos`, and `Real.pi` from the imported Physlib/Mathlib
  infrastructure.

## Local abstractions introduced

- `RestMassQuantity := Dimensionful (WithDim M𝓭 NNReal)` preserves a
  nonnegative physical mass independently of units.  This is a genuine
  dimensionful type, not a scalar alias or one-field scalar wrapper.
- `SatisfiesRelativisticReactionLaws` is a local law interface because the
  search did not expose a ready-made relativistic reaction/four-momentum
  conservation structure.  Its fields state the general on-shell and
  conservation laws rather than this problem's numerical answer.
- Figure-specific inductives and `KaonProtonReactionFigure` preserve the
  panel labels, axes, particle identities, and raster-derived directions
  without pretending that those qualitative data are numerical dynamics.

## Grounding gaps and redraft requests

- LeanExplore exposed no ready-made relativistic two-body collision or
  four-momentum conservation API compatible with this setup.  The local law
  interface is therefore the smallest faithful substitute.
- No dedicated `DimMass` declaration appeared in the searches.  The local
  rest-mass type uses the underlying Physlib dimension system directly.
- The auxiliary caption says the pion angle is measured from the `y`-axis,
  but the primary raster shows the marked angle between the pion trajectory
  and `+x`.  Following the chapter's instruction to use the image as primary
  evidence, the Lean figure model uses the `+x` interpretation.
- The requested `.archon/AGENTS.md` file and the `archon` executable were not
  present in this workspace.  The available
  `.archon/prover-modes/physics-formalize.md` role document was used instead.
- The blueprint theorem environment was not marked with `\\leanok`: the task's
  explicit write-permission section allows edits only to the assigned Lean
  file and this task-result file and expressly forbids editing blueprint
  chapters.  A coordinator with blueprint write authority should add the
  marker.

## Verification

- `archon-lean-lsp` diagnostics: only the expected `declaration uses sorry`
  warning at the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0554.lean`: exit code 0,
  with only the expected `sorry` warning.

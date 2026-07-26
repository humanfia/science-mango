# Autoformalization result: `problem_phyx_mini_0593.lean`

## Assumption/target split

### Governing laws

- `SatisfiesRelativisticEmissionClockLaw.emissionIntervalTimeDilation` states the generic special-relativistic clock relation `τ = γ(v/c) τ₀` between the co-moving mechanical timer and the interval between emissions measured in `S`. It does not mention `τ_R`.
- `SatisfiesRecedingRadarPulseKinematics.sourceRecedesBetweenEmissions` states that the source--receiver separation grows by `v τ` between emissions.
- `firstPulseTravelsAtLightSpeed` and `secondPulseTravelsAtLightSpeed` independently state `distance = c × flight time` for each left-moving pulse.
- `receiverArrivalIntervalAccounting` identifies the arrival-time difference as the emission-time difference plus the difference of the two independent flight durations.
- `HasPhysicalRadarParameters` supplies positive speed, strict subluminality, positive periods/flight times, positive separations, and positive vacuum light speed. It gives no Doppler factor or target interval value.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- `MatchesRadarPulseScenario` assigns receiver `R` to stationary frame `S`, transmitter `T` and its mechanical timer to moving frame `S'`, the trigger/emitter/detector roles, rightward recession, and leftward radar-pulse propagation.
- `RadarPulseFigure` and `MatchesSuppliedRadarFigure` preserve the primary raster's left/right frame placement, apparatus placement, transmitter--timer connection, `τ₀` timer-box label, velocity arrow on `S'`, left-moving wavefronts, and the otherwise physically uninterpreted baseline label `A`.
- The four printed answer formulas are retained by `AnswerChoice`, `displayedArrivalIntervalFactor`, and `displayedArrivalIntervalReadout`. `recordedDatasetAnswer` records `.C` as source metadata only.

### Current target conclusions

- `problem_phyx_mini_0593` concludes, in every selected time unit, `τ₀ < τ < τ_R` for strictly positive receding speed.
- It explicitly concludes, in every coherent length/time unit,
  `τ_R = τ₀ * Real.sqrt ((c + v) / (c - v))`.
- `receiverArrivalInterval_from_kinematics` is an intermediate conclusion deriving `τ_R = τ (c + v) / c` solely from the two-pulse propagation equations.

## Goal-faithfulness audit

- `receiverArrivalIntervalTauR`, `referenceFrameEmissionIntervalTau`, and `properTimerPeriodTau0` are independent dimensionful fields; none is defined from another or from an answer choice.
- No premise contains the square-root Doppler relation, the strict target inequalities, or a problem-specific value of `τ_R`.
- The clock-law premise stops at the generic time-dilation relation for `τ`, while the propagation premise is expressed through two separations and two flight durations rather than through the requested final Doppler factor.
- Although choice C necessarily records the formula printed in the multiple-choice data, neither `displayedArrivalIntervalFactor` nor `recordedDatasetAnswer` occurs in a theorem hypothesis or in the theorem conclusion. Unfolding those metadata definitions cannot prove the physical theorem.
- The initial source--receiver separation is retained and cancels only in the helper lemma; it was not silently omitted from the physical model.
- The literal figure label `A` is preserved without guessing that it denotes a physical length or event.

## Declarations and blueprint labels

- `problem_phyx_mini_0593` formalizes `thm:physics:phyx_mini_0593:target`.
- `receiverArrivalInterval_from_kinematics` is an unlabeled local helper declaration supporting that target.
- Supporting declarations: dimensionful quantity/readout definitions; frame, apparatus, direction, signal, figure-label, and answer-choice types; `RadarPulseFigure`; `RadarPulseTimingSetup`; scenario/figure/physical/law structures; and displayed-choice metadata.
- The target statement is ready for the blueprint's theorem environment to receive `\lean{PhyXMiniProblems.ProblemPhyXMini0593.problem_phyx_mini_0593}` and the autoformalized-statement marker. The blueprint was not edited because prover write permissions restrict this lane to the assigned Lean file and task result.

## LeanExplore queries/candidates actually used

- `Lorentz factor special relativity gamma` and `LorentzGroup.γ` found `LorentzGroup.γ` (id 391166). Its fetched source is `def γ (β : ℝ) : ℝ := 1 / Real.sqrt (1 - β^2)` in `Physlib.Relativity.LorentzGroup.Boosts.Basic`; this is used by `movingFrameLorentzFactor`.
- `dimensionful physical quantity units WithDim time duration` found `Dimensionful` (id 394284) in `Physlib.Units.Basic`; its source confirms that it represents unit-choice-dependent values satisfying dimensional scaling.
- `WithDim` found `WithDim` (id 394425) in `Physlib.Units.WithDim.Basic`; its fetched source confirms the dimension-tagged carrier used for length and duration quantities.
- `DimSpeed speedOfLight vacuum speed of light` found `DimSpeed` (id 394481) and `DimSpeed.speedOfLight` (id 394486) in `Physlib.Units.WithDim.Speed`. Fetched source confirms that `DimSpeed` is a nonnegative dimensionful speed and `speedOfLight` is the exact `299792458 m/s` dimensionful constant.
- `TimeUnit LengthUnit UnitChoices` found `TimeUnit` (id 393613), `LengthUnit` (id 393137), and `UnitChoices` (id 394255), used at scalar readout boundaries.
- `Real.sqrt square root` and the likely-name query `Real.sqrt` found `Real.sqrt` (id 143113) in `Mathlib.Analysis.Real.Sqrt`; its source was fetched and the name is used in the displayed formulas and final target.

## PhysLean/Mathlib names grounded

- Mathlib: `Real.sqrt`.
- PhysLean/Physlib namespace: `Dimensionful`, `WithDim`, `Dimension.T𝓭`, `Dimension.L𝓭`, `LengthUnit`, `TimeUnit`, `UnitChoices`, `DimSpeed`, `DimSpeed.speedOfLight`, and `LorentzGroup.γ`.

## Local abstractions introduced

- `RadarPulseTimingSetup` is the smallest local aggregate keeping the three distinct time observables, relative speed, two source separations, and two pulse flight durations physically separate.
- `RadarPulseFigure` plus small enumerations preserve the primary-image labels and geometry without assigning unsupported numerical values.
- The scenario, physical-domain, clock-law, and pulse-kinematics structures separate role/data assumptions from governing physics. They were introduced because no searched PhysLean declaration models this complete moving-transmitter/two-pulse arrival experiment.
- No basic physical quantity was collapsed to a transparent real alias: durations and lengths use Physlib's dimensionful quantities, speed uses `DimSpeed`, and real values appear only through explicitly unit-labelled readouts.

## Grounding gaps

- LeanExplore exposed the Lorentz factor, unit infrastructure, exact vacuum light speed, and real square root, but no ready-made relativistic radar pulse-arrival or longitudinal Doppler-period object. The local two-pulse kinematics interface fills that gap while preserving the physical derivation and keeping the current target out of the premises.
- The requested `.archon/AGENTS.md` was absent from this project checkout. The prover role and blueprint-write restriction were recovered from the installed Archon template and `.archon/prover-modes/physics-formalize.md`.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly two expected `declaration uses sorry` warnings, for the helper lemma and final theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0593.lean` exited successfully with only those same two expected warnings.

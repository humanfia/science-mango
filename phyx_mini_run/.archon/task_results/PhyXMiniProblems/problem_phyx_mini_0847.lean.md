# Autoformalization result: `problem_phyx_mini_0847.lean`

## Outcome

Created a compiling physics formalization with `by sorry` bodies for the two
substantive declarations. Direct verification with
`lake env lean PhyXMiniProblems/problem_phyx_mini_0847.lean` exits successfully
and reports only the two expected `declaration uses sorry` warnings.

The primary bitmap, rather than its inconsistent auxiliary caption, was used
for the topology: the `-1 nC` charge is in the bounded solid-torus region and
the `+100 nC` charge is in the central hole, hence outside the volume bounded
by the toroidal surface.

## Assumption/target split

### Governing laws

- `SatisfiesTorusGaussLaw.enclosedChargeAccounting` sums the physical charges
  using a general enclosure weight determined by each charge's region.
- `SatisfiesTorusGaussLaw.integralGaussLaw` states integral Gauss's law as
  `Phi_E = Q_enclosed / epsilon_0` in coherent SI readouts.
- `HasPhysicalTorusParameters` supplies positive tube radius, a tube radius
  smaller than the major radius, and positive vacuum permittivity.
- `UsesTextbookVacuumPermittivity` supplies the standard textbook numerical
  calibration `8.85 * 10^-12 C^2/(N m^2)` used by the estimate.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- The primary figure is a closed toroidal surface and supplies no calibrated
  radius scale.
- The minus-marked charge has readout `-1 nC` and lies in the solid-torus
  interior.
- The plus-marked charge has readout `+100 nC` and lies in the torus's central
  hole, which has enclosure weight zero.
- The four displayed flux values are `120`, `-100`, `200`, and `-110` in
  `N m^2/C` for choices A through D.

### Current target conclusions

- `enclosed_charge_of_supplied_torus_figure`: the net enclosed charge has
  readout `-1 nC`.
- `problem_phyx_mini_0847`: the model flux is exactly
  `-20000/177 N m^2/C`, is within `3 N m^2/C` of the displayed `-110`, and D
  is the unique closest answer choice.

## Goal-faithfulness audit

`TorusElectrostaticsSetup.netEnclosedCharge` and `netElectricFlux` are
independent dimensionful fields. Neither is defined by the desired answer.
The Gauss-law structure contains only the general charge-accounting and
integral-law equations; it contains no `-110`, no `-20000/177`, and no answer
label. The textbook permittivity hypothesis is the conventional
`8.85 * 10^-12` calibration rather than a reverse-engineered constant chosen
to force `-110`. The answer-choice table is source data, while
`IsUniqueClosestAnswerChoice` is generic in the choice and does not privilege
D. Both numerical flux conclusions remain solely on the conclusion side of
the main theorem.

## Declarations and blueprint labels

- Dimensionful quantities/readouts: `ChargeQuantity`, `LengthQuantity`,
  `VacuumPermittivityQuantity`, `ElectricFluxQuantity`,
  `vacuumPermittivityDimension`, `electricFluxDimension`, and named SI
  readout functions.
- Figure and geometry: `FigureCharge`, `ChargeSignMark`,
  `TorusRelativeRegion`, `torusEnclosureWeight`, `TorusGaussianSurface`,
  `TorusChargeFigure`, and `TorusElectrostaticsSetup`.
- Assumption interfaces: `HasPhysicalTorusParameters`,
  `MatchesSuppliedTorusFigure`, `UsesTextbookVacuumPermittivity`, and
  `SatisfiesTorusGaussLaw`.
- Multiple-choice vocabulary: `AnswerChoice`, `displayedFluxValue`, and
  `IsUniqueClosestAnswerChoice`.
- Derived lemma: `enclosed_charge_of_supplied_torus_figure`.
- Main declaration: `problem_phyx_mini_0847`, corresponding to
  `thm:physics:phyx_mini_0847:target`.

The blueprint chapter already exists. It was not edited to add `\leanok`
because the task's final write-permission section explicitly restricts edits
to the assigned Lean file and this result file; blueprint synchronization is
therefore pending the plan/orchestration agent.

## LeanExplore queries and candidates actually used

The following searches were run in this post-formalization iteration with
`packages: ["Mathlib", "Physlib"]`:

- Natural-language concepts:
  - `Gauss law electric flux through a closed surface equals enclosed charge divided by vacuum permittivity`
  - `Dimensionful WithDim UnitChoices.SI physical quantity dimension chosen units`
  - `vacuum permittivity electric charge SI dimensions`
  - `toroidal closed surface electric flux enclosed point charge`
- Likely Lean names:
  - `WithDim`
  - `Dimension.C𝓭`
  - `Dimension.L𝓭`
  - `UnitChoices.SI_charge`

Source, module, and docstring data were fetched only for declarations selected
for the model: `Dimensionful` (result 394284), `WithDim` (394425),
`UnitChoices.SI` (394270), `Dimension` (394292), `Dimension.C𝓭` (394337),
`Dimension.L𝓭` (394324), `Dimension.T𝓭` (394330), and `Dimension.M𝓭`
(394336). LeanExplore located them in `Physlib.Units.Basic`,
`Physlib.Units.WithDim.Basic`, and `Physlib.Units.Dimension`.

## PhysLean/Mathlib names grounded

- `Dimensionful` and `WithDim` provide unit-independent, dimension-tagged
  physical quantities.
- `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, and
  `Dimension.C𝓭` ground the length, time, mass, and charge dimensions.
- `UnitChoices.SI` grounds coherent SI readouts. Its fetched source explicitly
  sets the base units to metres, seconds, kilograms, coulombs, and kelvin.
- `NNReal` represents nonnegative lengths and permittivity; signed charge and
  flux use real-valued carriers inside the dimensionful wrapper.

## Local abstractions introduced

- `vacuumPermittivityDimension` and `electricFluxDimension` encode the exact
  SI dimensions absent as named PhysLean declarations.
- `TorusGaussianSurface` retains the major/tube-radius geometry even though
  the image has no length calibration.
- `TorusRelativeRegion` distinguishes bounded solid interior, central hole,
  and exterior; this preserves the topological fact essential to Gauss's law.
- `TorusChargeFigure` separates visual labels/readouts from physical charge
  quantities.
- `SatisfiesTorusGaussLaw` is a faithful local interface for the unavailable
  integral Gauss-law API.

These abstractions preserve physical roles and dimensions rather than
collapsing charge or flux to transparent scalar aliases.

## Grounding gaps

The Gauss-law and toroidal-flux searches returned Physlib declarations for
electric fields, point-particle field divergence, Coulomb's constant, and
free-space permittivity facts, but no declaration for electric flux through a
closed surface or integral Gauss's law. Those results do not supply a
dimensionful flux quantity or the required surface-integral law, so the local
dimensionful permittivity and Gauss-law interface were retained.

The requested project-local `.archon/AGENTS.md` does not exist. The available
`.archon/prover-modes/physics-formalize.md` was read as the applicable role
document, together with the injected task instructions.

The requested `archon dag-query` navigation could not be run because the
`archon` executable is not on `PATH` in this workspace session. No blueprint
ancestor dependency was therefore imported.

## Redraft requests

None for the physics statement. Blueprint `\leanok` synchronization remains
for an agent with blueprint write permission.

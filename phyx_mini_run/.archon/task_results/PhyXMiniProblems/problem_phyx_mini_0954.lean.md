# Post-formalization result: `problem_phyx_mini_0954.lean`

## Review disposition

The blueprint chapter contains `% archon:physics`, so the
`physics-formalize` discipline was applied. This was the final semantic
retry. The exact gate defect was that the source never defines `sigma`, while
the former theorem asserted
`RotatesMoreThanHalfTurn setup ↔ halfTurnSigmaThreshold < setup.sigma`
without any physical law relating `setup.sigma` to the field, geometry,
energy, torque, or trajectory.

The source report and primary image `phyx_data/test_image/954.png` were
audited. The raster shows the cylinder, radial `R` guide, axial `W` guide,
diametral winding, upward visible current arrow `I`, downward field arrow
`B`, a black material attachment point on the rim, the vertical cable and
mass `M`, the height `h`, and a pale ghost of that same mass at its lowest
position. It supports a fixed rim attachment, not circumference payout.
Accordingly, the geometry now states
`h(theta) = R * (1 - cos theta)` and `h_top = 2 R`.

The unsupported sigma equivalence was replaced by the strongest
source-supported symbolic relation. The theorem first derives the explicit
potential `M g R (1 - cos theta) - (N I 2 R W) B cos(theta + offset)` from the
loop, geometry, and energy laws. Release from rest identifies the release
energy with the initial potential energy, and passage beyond a half-turn makes
every intermediate travel through `pi` reachable with kinetic energy equal to
the drop in potential and with potential energy no greater than its initial
value. The displayed sigma propositions and recorded choice B remain metadata
only.

The requested `.archon/AGENTS.md` does not exist in this project. The
available `.archon/prover-modes/physics-formalize.md`, `.archon/PROGRESS.md`,
the exact review-gate entry, the source report, blueprint, assigned Lean file,
and primary raster were read. The advertised `archon` executable is also
absent, so no DAG query could be run.

## Assumption/target split

### Governing laws

- The rectangular diametral loop area is `A = 2 R W`.
- The winding magnetic-moment magnitude obeys `mu = N I A`.
- The external Physlib magnetic vector field is uniform and downward.
- The cable is fixed to a material point on the rim; with attachment angle
  measured from downward, `h(theta) = R (1 - cos theta)` and
  `h_top = 2 R`.
- The magnetic-moment axis and attachment coordinate have a fixed angular
  offset.
- Gravitational potential is `M g h`; magnetic potential is
  `-mu B cos phi`.
- The corresponding axial torques are `-M g R sin theta` and
  `-mu B sin phi`, and net torque is their sum.
- Angular position is continuous, angular velocity is its SI-time derivative,
  rotational kinetic energy is `J omega^2 / 2`, and mechanical energy is
  conserved after release.

### Previous-part results

- None. The source report has `previous_parts: []`.
- In particular, no previous-part definition or calibration of `sigma` is
  available.

### Figure/data readouts

- The cylinder, diametral winding, horizontal axle, fixed rim attachment,
  vertical cable, hanging mass, and lowest-position ghost.
- Raster labels `R`, `W`, `I`, `B`, `M`, and `h`; the turn count
  `N` comes from the prose and is explicitly recorded as absent from the
  raster.
- The magnetic-field arrow points downward and the visible current arrow
  points upward.
- The mass is released from rest at its top height.
- The four displayed sigma conditions and recorded answer B are answer-sheet
  metadata, not physical data.

### Current target conclusions

- For some fixed coil-axis offset, the total potential in coherent SI units is
  `M g R (1 - cos theta) - (N I 2 R W) B cos(theta + offset)`.
- Release from rest implies that the initial mechanical energy equals the
  initial potential energy.
- If `RotatesMoreThanHalfTurn setup`, then for every
  `travelRadians ∈ Set.Icc 0 Real.pi` there is a nonnegative time at which
  that oriented travel is attained.
- At that time the kinetic energy equals the initial mechanical energy minus
  the potential energy at the corresponding attachment angle; the theorem
  states this using the equal initial potential energy.
- Consequently, the potential energy at every such intermediate angle is at
  most the initial potential energy.
- No numerical or sigma-threshold conclusion is asserted.

## Goal-faithfulness audit

`MagneticLiftSetup` contains independent apparatus quantities, observables,
and a trajectory. The disconnected `sigma : ℝ` field was removed entirely.
The identifier `sigma` now occurs only as the explicit argument of
`displayedSigmaCondition`, which transcribes answer-sheet metadata and is
neither a theorem premise nor conclusion.

`RotatesMoreThanHalfTurn` is defined only from the independent angular
trajectory. `MatchesProblemAndPrimaryFigure` contains source measurements and
qualitative raster facts. The four governing-law structures contain geometry,
electromagnetism, potentials, torques, kinematics, kinetic energy, and
conservation, but no half-turn reachability criterion. In particular, the old
`rotationPastHalfTurnCriterion` premise field was removed. Thus the repaired
energy conclusion is not available by projection from a premise and is not
made true by unfolding a target-shaped local definition.

The symbolic conclusion follows by the intended future proof route:
the loop-area, magnetic-moment, fixed-rim height, axis-offset, and two
potential-energy laws give the explicit apparatus potential; continuity and
the intermediate value theorem supply a time for every travel between zero
and a witness beyond `pi`; the release-from-rest and kinetic-energy laws
identify the initial mechanical and potential energies; conservation gives
the exact later kinetic-energy identity; and nonnegative inertia gives the
potential-energy inequality. These are general physical and mathematical
laws, not restatements of the target.

The historical theorem name
`rotatesMoreThanHalfTurn_iff_sigma_gt_threshold` is retained solely to
preserve the existing blueprint pin, following the project's final-retry
convention. Its former iff statement is not asserted.

Physical primitives are not transparent aliases to `ℝ`. Length, area, mass,
current, magnetic flux density, acceleration, magnetic moment, inertia,
torque, angular velocity, and energy all use Physlib
`Dimensionful (WithDim ...)` or `DimEnergy`. Real numbers occur only in
named coherent-unit readouts, angles, time-in-seconds coordinates, and
answer-sheet metadata.

## Declarations and blueprint labels

All retained public declarations already have topology entries in the chapter:

| Lean declaration | Blueprint label |
| --- | --- |
| `electricCurrentDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-electriccurrentdimension` |
| `magneticFluxDensityDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticfluxdensitydimension` |
| `accelerationDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-accelerationdimension` |
| `magneticMomentDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticmomentdimension` |
| `momentOfInertiaDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-momentofinertiadimension` |
| `torqueDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-torquedimension` |
| `angularVelocityDimension` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-angularvelocitydimension` |
| `LengthMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-lengthmagnitude` |
| `AreaMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-areamagnitude` |
| `MassMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-massmagnitude` |
| `ElectricCurrentMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-electriccurrentmagnitude` |
| `MagneticFluxDensityMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticfluxdensitymagnitude` |
| `AccelerationMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-accelerationmagnitude` |
| `MagneticMomentMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticmomentmagnitude` |
| `MomentOfInertiaMagnitude` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-momentofinertiamagnitude` |
| `AxialTorqueQuantity` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-axialtorquequantity` |
| `AngularVelocityQuantity` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-angularvelocityquantity` |
| `EnergyQuantity` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-energyquantity` |
| `nonnegativeReadout` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-nonnegativereadout` |
| `signedReadout` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-signedreadout` |
| `energyInJoules` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-energyinjoules` |
| `FigureObject` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-figureobject` |
| `FigureLabel` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-figurelabel` |
| `VerticalDirection` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-verticaldirection` |
| `WindingGeometry` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-windinggeometry` |
| `CableAttachment` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-cableattachment` |
| `DepictedCurrentSense` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-depictedcurrentsense` |
| `MagneticLiftFigure` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticliftfigure` |
| `SpatialVector` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-spatialvector` |
| `downwardUnitVector` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-downwardunitvector` |
| `MagneticLiftSetup` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-magneticliftsetup` |
| `initialAttachmentAngle` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-initialattachmentangle` |
| `totalPotentialEnergyInJoules` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-totalpotentialenergyinjoules` |
| `mechanicalEnergyInJoulesAtTime` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-mechanicalenergyinjoulesattime` |
| `orientedAngularTravelAtTime` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-orientedangulartravelattime` |
| `RotatesMoreThanHalfTurn` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-rotatesmorethanhalfturn` |
| `MatchesProblemAndPrimaryFigure` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-matchesproblemandprimaryfigure` |
| `HasPhysicalMagneticLiftParameters` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-hasphysicalmagneticliftparameters` |
| `SatisfiesCurrentLoopAndUniformFieldLaws` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-satisfiescurrentloopanduniformfieldlaws` |
| `SatisfiesRigidCylinderAndCableGeometry` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-satisfiesrigidcylinderandcablegeometry` |
| `SatisfiesMagneticAndGravitationalEnergyLaws` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-satisfiesmagneticandgravitationalenergylaws` |
| `SatisfiesConservativeRotationalDynamics` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-satisfiesconservativerotationaldynamics` |
| `AnswerChoice` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-answerchoice` |
| `halfTurnSigmaThreshold` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-halfturnsigmathreshold` |
| `displayedSigmaCondition` | `def:physics:phyx-mini-0954:phyxminiproblems-problemphyxmini0954-displayedsigmacondition` |
| `rotatesMoreThanHalfTurn_iff_sigma_gt_threshold` | `thm:physics:phyx_mini_0954:target` |

`recordedDatasetAnswer` is private answer-sheet metadata and intentionally
has no public blueprint node.

## LeanExplore queries and candidates actually used

Every search passed `packages: ["Mathlib", "Physlib"]`.

- Natural language `magnetic dipole potential energy torque current loop in a
  uniform magnetic field` returned electromagnetic-potential declarations,
  but no finite current-loop magnetic-moment, dipole-potential, or torque law
  matching this apparatus.
- Natural language `dimensionful physical quantities SI units energy magnetic
  field` selected `Dimensionful` (id `394284`), `UnitChoices.SI`
  (id `394270`), `Electromagnetism.MagneticField` (id `385560`), and
  led to the dedicated energy search.
- Natural language `continuous real function reaches every value between
  endpoint values intermediate value theorem` selected
  `intermediate_value_Icc` (id `351393`) as the intended future proof
  route for reaching every intermediate angular travel.
- Likely-name search
  `Electromagnetism.MagneticField Dimensionful DimEnergy UnitChoices.SI`
  reconfirmed the three Physlib infrastructure declarations.
- Likely-name search `DimEnergy energy quantity joule` selected
  `DimEnergy` (id `394468`).

Source code, module, and docstring were fetched for all five selected
candidates: `Dimensionful`, `UnitChoices.SI`,
`Electromagnetism.MagneticField`, `DimEnergy`, and
`intermediate_value_Icc`.

## Physlib/Mathlib names grounded

- `Dimensionful` from `Physlib.Units.Basic`: unit-choice-indexed physical
  representations satisfying a dimension-scaling law.
- `UnitChoices.SI` from `Physlib.Units.Basic`: metres, seconds, kilograms,
  coulombs, and kelvin.
- `DimEnergy` from `Physlib.Units.WithDim.Energy`: signed dimensionful
  energy with dimension `M L² T⁻²`.
- `Electromagnetism.MagneticField 3` from
  `Physlib.Electromagnetism.Basic`: a spacetime-dependent
  `EuclideanSpace ℝ (Fin 3)` field.
- `intermediate_value_Icc` from
  `Mathlib.Topology.Order.IntermediateValue`: the closed-interval
  intermediate value theorem underlying the intended proof.
- The elaborated file also uses Mathlib `NNReal`, `EuclideanSpace`,
  `Continuous`, `HasDerivAt`, `Set.Icc`, `Real.sin`, `Real.cos`, and
  `Real.pi`, together with Physlib `WithDim`, `Dimension`, and the
  constructors `L𝓭`, `T𝓭`, `M𝓭`, and `C𝓭`.

## Local abstractions introduced

- The dimensionful magnitude aliases assemble exact physical dimensions from
  grounded Physlib primitives. They are not transparent real-scalar aliases;
  named readouts are the only maps to `ℝ`.
- `MagneticLiftFigure` and its finite vocabularies preserve literal raster
  labels, directions, attachment kind, winding geometry, and the
  lowest-position ghost.
- `MagneticLiftSetup` stores independent apparatus quantities, fields,
  energies, torques, and trajectory observables. It contains no undefined
  answer-determining scalar.
- `SatisfiesCurrentLoopAndUniformFieldLaws`,
  `SatisfiesRigidCylinderAndCableGeometry`,
  `SatisfiesMagneticAndGravitationalEnergyLaws`, and
  `SatisfiesConservativeRotationalDynamics` are the smallest local
  governing-law interfaces needed because no reusable library model covers
  this coupled coil-cylinder-mass apparatus.
- The real angular trajectory is intentionally unwrapped: a periodic
  `Real.Angle` value cannot distinguish travel beyond a half-turn.
- `AnswerChoice`, `halfTurnSigmaThreshold`,
  `displayedSigmaCondition`, and private `recordedDatasetAnswer` isolate
  the source's printed response data from the physical model.

## Grounding gaps

- LeanExplore found no Physlib/Mathlib law for the magnetic moment and torque
  of this finite diametral winding or for the coupled rigid-rim mass dynamics;
  faithful local law interfaces were necessary.
- Physlib's `Electromagnetism.MagneticField` is a real-vector-valued field,
  not itself tagged with tesla dimensions. The model therefore retains a
  separate dimensionful field magnitude and calibrates the uniform vector
  field to it.
- The source's substantive gap remains: `sigma` is never defined. No
  threshold in that symbol can be derived from `R`, `W`, `N`, `I`,
  `B`, `M`, and `g` without an external normalization. The formalization
  does not guess one.
- The generic laws prove a necessary energy condition for passage beyond a
  half-turn. A sufficient iff criterion would require a more detailed,
  non-stalling rotational ODE model that the isolated source does not state.

## Iteration 020 prover result

Status: complete. The sole `sorry` in
`rotatesMoreThanHalfTurn_iff_sigma_gt_threshold` was replaced by a proof
without changing the declaration header, hypotheses, or conclusion.

The proof:

- substitutes the fixed coil-axis offset, rim-height law, gravitational and
  magnetic potential laws, coil-area law, and magnetic-moment law, then closes
  the explicit potential identity by ring normalization;
- uses release from rest and the rotational kinetic-energy law to identify the
  initial mechanical and potential energies;
- applies `intermediate_value_Icc` to the continuous oriented angular travel
  between release and the supplied beyond-half-turn witness;
- uses the two allowed release signs to recover the corresponding attachment
  angle;
- combines conservation of mechanical energy with nonnegativity of the
  dimensionful inertia readout and the squared angular velocity to obtain the
  kinetic-energy identity and potential-energy inequality.

No redraft is needed and no proof blocker remains. The earlier formalization
marker requests are obsolete because the current blueprint target prose now
matches the theorem. The target environment was not edited to add `\leanok`
because the prover task explicitly permits writes only to the assigned Lean
file and this result file; the plan/polish stage should add that marker.

The requested `.archon/AGENTS.md` is absent from this project. The available
physics prover-mode instructions were read and followed.

## Verification

- Lean LSP diagnostics report no errors, warnings, or failed dependencies.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0954.lean` exits `0`
  with no output.
- A source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide` in the assigned file.
- `lean_verify` reports no suspicious-source warnings. Its dependency axiom
  list contains only Mathlib's standard `propext`, `Classical.choice`, and
  `Quot.sound`.

# Autoformalization result: `problem_phyx_mini_0707.lean`

## Status

This is the genuine iteration-003 post-formalization report requested by the
review gate.  I re-read the current 346-line Lean model, the linked blueprint,
the source report, and the primary raster `phyx_data/test_image/707.png`; I also
reran the LeanExplore grounding queries and both compilation checks recorded
below.  The assigned Lean file is a compiling physics formalization of the
supplied forearm-statics problem. It retains the conflict between the prose
question and the primary image as typed data/metadata, while the theorem states
the physically supported results from the printed values and equilibrium laws:

- tendon-force magnitude: `7875 / 2 = 3937.5 N`;
- elbow-reaction magnitude: `6975 / 2 = 3487.5 N`;
- recorded choice C (`3900 N`) is uniquely nearest to the tendon magnitude;
- choice D (`3700 N`) is uniquely nearest among the displayed choices to the elbow-reaction magnitude.

The existing iteration-002 redraft already had the required semantics.  The
iteration-003 audit found no semantic defect, so the Lean declaration interface
was preserved rather than replaced merely to create textual churn.

## Assumption/target split

### Governing laws

- `SatisfiesForearmStaticEquilibrium.netForceIsZero` states that the three physical planar force vectors have zero coherent-SI resultant.
- `SatisfiesForearmStaticEquilibrium.netTorqueAboutElbowIsZero` states that the signed planar torques of the tendon, elbow reaction, and barbell about the elbow sum to zero.
- `planarTorqueInNewtonMeters` is the generic out-of-plane component of `(applicationPoint - pivot) × force`, namely `rₓ Fᵧ - rᵧ Fₓ`, at the coherent-SI readout boundary. It contains no problem-specific force answer.

### Previous-part results

- None. The source report has `previous_parts: []`; no requested force magnitude is assumed from an earlier part.

### Figure/data readouts

- `MatchesSuppliedFigure` records all three arrows, all five printed quantity labels, their directions and application points, the upper-arm/forearm orientation, the tendon attachment lying between elbow and barbell end, the elbow-torque arc, the known-data block, and the image's `Find F_tendon` block.
- `MatchesProblemReadouts` records `d_tendon = 4.0 cm`, `d_arm = 35 cm`, and `|F_barbell| = 450 N`.
- `MatchesForearmGeometry` realizes the elbow as the origin and both application points along the horizontal forearm with the two named physical lever-arm lengths.
- `MatchesDisplayedForceDirections` records vertical forces, with the tendon upward and the elbow reaction and barbell force downward. It does not prescribe either unknown magnitude.
- `displayedForceInNewtons` transcribes A = 3800, B = 4000, C = 3900, and D = 3700. `recordedAnswerChoice` transcribes the dataset's recorded C as metadata.

### Current target conclusions

- `problem_phyx_mini_0707` concludes the exact tendon magnitude `7875 / 2`, the exact elbow-reaction magnitude `6975 / 2`, unique-nearest choice C for the tendon force, and unique-nearest choice D for the elbow reaction.
- These conclusions reconcile the two source objectives without asserting the physically false equation `|F_elbow| = 3900 N`.

## Source/law/answer audit

- Primary-image evidence actually inspected: the upper arm is vertical, the
  forearm is horizontal, the upward tendon arrow is applied between the elbow
  and barbell end, the elbow and barbell arrows point downward, and the printed
  blocks read `d_tendon = 4.0 cm`, `d_arm = 35 cm`, `F_barbell = 450 N`, and
  `Find F_tendon`.  The dashed blue annotation says these forces cause torques
  about the elbow.
- Source-report evidence: the prose asks for `|F_elbow|`, the answer options are
  3800, 4000, 3900, and 3700 N, the recorded answer is C = 3900 N, and
  `previous_parts` is empty.
- Governing-law status: zero net force and zero net torque are statics-model
  assumptions, not literal image readouts and not requested answers.  The
  application-point geometry and arrow orientations connect those laws to this
  particular figure.
- Physical calculation represented by the target: torque balance gives
  `0.04 F_tendon = 0.35 * 450`, hence `F_tendon = 3937.5 N`; vertical force
  balance then gives `F_elbow = 3937.5 - 450 = 3487.5 N` downward.
- Answer audit: C = 3900 N is uniquely nearest to the tendon result, while
  D = 3700 N is uniquely nearest to the elbow result.  Thus the recorded answer
  agrees with the image's requested quantity but not with the prose question;
  the theorem exposes rather than hides that inconsistency.

## Goal-faithfulness audit

- `ForearmStaticsSetup` stores independent dimensionful positions, physical lengths, and force vectors. Neither unknown force is defined from a displayed answer.
- No premise field contains `7875 / 2`, `6975 / 2`, a nearest-choice result, or a selected answer for either unknown force.
- `recordedAnswerChoice = .C` is source metadata only. The substantive statement that C is nearest to the tendon magnitude remains in the theorem conclusion.
- `displayedForceInNewtons` merely transcribes the offered values; `IsNearestDisplayedForce` and `IsUniqueNearestDisplayedForce` compare an independently modeled force observable with those values.
- The image's `Find F_tendon` block is kept in `MatchesSuppliedFigure`, while the prose request for the elbow magnitude is represented by the theorem's separate elbow conclusion. The two forces are never identified.
- The governing statics predicate contains only zero-resultant and zero-torque laws, not a disguised form of either current numerical conclusion.

## Declarations and blueprint correspondence

- Physical dimensions and quantity types: `forceDimension`, `torqueDimension`, `LengthQuantity`, `PlanarPositionQuantity`, `PlanarForceQuantity`, and `PlanarTorqueQuantity`.
- Coherent-SI readouts/mechanics: `xAxis`, `yAxis`, `lengthInMeters`, `lengthInCentimeters`, `positionInMeters`, `forceVectorInNewtons`, `forceMagnitudeInNewtons`, and `planarTorqueInNewtonMeters`.
- Figure/model vocabulary: `AppliedForceLabel`, `ApplicationPointLabel`, `FigureElement`, `FigureQuantityLabel`, `ArrowDirection`, `expectedArrowDirection`, `expectedApplicationPoint`, `ForearmStaticsFigure`, and `ForearmStaticsSetup`.
- Assumption interfaces: `MatchesSuppliedFigure`, `MatchesProblemReadouts`, `MatchesForearmGeometry`, `MatchesDisplayedForceDirections`, and `SatisfiesForearmStaticEquilibrium`.
- Answer/target declarations: `AnswerChoice`, `displayedForceInNewtons`, `recordedAnswerChoice`, `IsNearestDisplayedForce`, `IsUniqueNearestDisplayedForce`, and `problem_phyx_mini_0707`.
- Blueprint label `thm:physics:phyx_mini_0707:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0707.problem_phyx_mini_0707`.

Every non-target declaration is explicitly pinned in the blueprint under label
prefix `def:physics:phyx-mini-0707:phyxminiproblems-problemphyxmini0707-`.
The exact declaration-to-label-suffix mapping is:

- `forceDimension` → `forcedimension`; `torqueDimension` → `torquedimension`;
  `LengthQuantity` → `lengthquantity`; `PlanarPositionQuantity` →
  `planarpositionquantity`; `PlanarForceQuantity` → `planarforcequantity`;
  `PlanarTorqueQuantity` → `planartorquequantity`.
- `xAxis` → `xaxis`; `yAxis` → `yaxis`; `lengthInMeters` → `lengthinmeters`;
  `lengthInCentimeters` → `lengthincentimeters`; `positionInMeters` →
  `positioninmeters`; `forceVectorInNewtons` → `forcevectorinnewtons`;
  `forceMagnitudeInNewtons` → `forcemagnitudeinnewtons`;
  `planarTorqueInNewtonMeters` → `planartorqueinnewtonmeters`.
- `AppliedForceLabel` → `appliedforcelabel`; `ApplicationPointLabel` →
  `applicationpointlabel`; `FigureElement` → `figureelement`;
  `FigureQuantityLabel` → `figurequantitylabel`; `ArrowDirection` →
  `arrowdirection`; `expectedArrowDirection` → `expectedarrowdirection`;
  `expectedApplicationPoint` → `expectedapplicationpoint`;
  `ForearmStaticsFigure` → `forearmstaticsfigure`; `ForearmStaticsSetup` →
  `forearmstaticssetup`.
- `MatchesSuppliedFigure` → `matchessuppliedfigure`; `MatchesProblemReadouts` →
  `matchesproblemreadouts`; `MatchesForearmGeometry` →
  `matchesforearmgeometry`; `MatchesDisplayedForceDirections` →
  `matchesdisplayedforcedirections`; `SatisfiesForearmStaticEquilibrium` →
  `satisfiesforearmstaticequilibrium`.
- `AnswerChoice` → `answerchoice`; `displayedForceInNewtons` →
  `displayedforceinnewtons`; `recordedAnswerChoice` → `recordedanswerchoice`;
  `IsNearestDisplayedForce` → `isnearestdisplayedforce`;
  `IsUniqueNearestDisplayedForce` → `isuniquenearestdisplayedforce`.

The blueprint was not edited because the autoformalize write-permissions block
allows changes only to the assigned Lean file and this task-result file.  Its
Lean links already exist; a blueprint-authorized plan/review/sync agent should
add `\leanok` after accepting the declaration.

## LeanExplore queries/candidates actually used

All searches passed `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `dimensionful physical quantity coherent SI units force length torque` found and grounded `UnitChoices.SI` (id 394270), `Dimensionful` (id 394284), `Dimension` (id 394292), and related unit-scaling declarations.
- Likely-name query `Dimensionful WithDim UnitChoices.SI` confirmed the Physlib unit-independent quantity API.
- Likely-name query `WithDim` found and grounded `WithDim` (id 394425).
- Natural-language query `planar cross product torque rigid body static equilibrium net force` found `crossProduct` (id 244738), `RigidBody.translational_equation_inertial` (id 385428), and `RigidBody.rotational_equation_inertial` (id 385429).
- Natural-language query `EuclideanSpace real finite-dimensional vector norm NNReal`
  found the relevant Euclidean norm API; likely-name query `EuclideanSpace`
  grounded `EuclideanSpace` (id 133893).
- Likely-name query `NNReal` grounded `NNReal` (id 211536) for nonnegative
  physical length readouts.

Source, module, and docstring were fetched after these searches for the
candidates used in the model: `Dimensionful`, `WithDim`, `UnitChoices.SI`,
`Dimension`, `EuclideanSpace`, and `NNReal`. They were also fetched for the
three statics/torque near-misses `crossProduct`,
`RigidBody.translational_equation_inertial`, and
`RigidBody.rotational_equation_inertial` to verify their mismatch rather than
guessing an API.

## Physlib/Mathlib names grounded

- Physlib: `Dimensionful` from `Physlib.Units.Basic`; `WithDim` from `Physlib.Units.WithDim.Basic`; `Dimension` and the basis dimensions `Dimension.L𝓭`, `Dimension.M𝓭`, and `Dimension.T𝓭`; `UnitChoices.SI` from `Physlib.Units.Basic`.
- Mathlib: `EuclideanSpace ℝ (Fin 2)` from `Mathlib.Analysis.InnerProductSpace.PiL2`, its Euclidean norm, and `NNReal` from `Mathlib.Data.NNReal.Defs`.

## Local abstractions introduced

- `LengthQuantity`, `PlanarPositionQuantity`, and `PlanarForceQuantity` combine Physlib's unit-independent `Dimensionful` quantities with dimension-tagged values. This preserves physical dimensions and planar vector direction instead of collapsing length or force to scalar aliases.
- `planarTorqueInNewtonMeters` provides the signed scalar torque appropriate to this two-dimensional figure. Its inputs remain dimensionful positions and forces; only the coherent-SI component readout is real-valued.
- The figure enums and `ForearmStaticsFigure` preserve the literal labels, geometry, arrow directions, and the conflicting displayed objective as typed evidence.
- `SatisfiesForearmStaticEquilibrium` is the smallest local governing-law interface for this problem. It states general force and torque balance and does not contain the numerical target.

## Grounding gaps and redraft requests

- No unresolved infrastructure gap blocks this formalization. The closest Physlib rigid-body declarations are `informal_lemma`s, so they cannot be premises in further Lean code. Mathlib's `crossProduct` is specifically for `(Fin 3 → R)` vectors, whereas this figure is modeled directly in `EuclideanSpace ℝ (Fin 2)`. The explicit planar determinant and local equilibrium predicate faithfully resolve those API mismatches.
- The source itself remains inconsistent: the image asks for `F_tendon`, the prose asks for `|F_elbow|`, and the recorded C = 3900 N matches only the tendon calculation after rounding. The formal theorem deliberately reports both exact physical magnitudes and both unique-nearest displayed choices. The blueprint/source owner may still wish to correct the prose target or dataset answer, but no Lean redraft is needed to expose the discrepancy honestly.
- The requested `.archon/AGENTS.md` was absent. `.archon/prover-modes/physics-formalize.md` was read as the available role specification.
- Both `archon dag-query node` and `archon dag-query ancestors` were attempted
  for `thm:physics:phyx_mini_0707:target`, but `archon` was not available on
  `PATH` in this runtime.
- The assigned file's `/- USER: ... -/` hint was read; it records that the file did not exist when the first autoformalization began.

## Verification

- `archon-lean-lsp` diagnostics: success, with only `declaration uses sorry` at `problem_phyx_mini_0707`.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0707.lean`: exit code 0, with only the expected `sorry` warning.

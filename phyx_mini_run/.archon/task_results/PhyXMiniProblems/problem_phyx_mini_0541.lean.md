# Autoformalization result: `problem_phyx_mini_0541.lean`

## Review-gate resolution

The exact review-2 reason was that this physics target did not directly import
Mathlib and therefore had not been checked in the real Lake/Mathlib
environment. This iteration added the focused direct import
`Mathlib.Analysis.InnerProductSpace.PiL2`, the module in which LeanExplore
locates `EuclideanSpace` and its `!₂[...]` notation. The physical declarations
and target were preserved because the prior semantic review passed and the
source audit below found no new defect.

## Assumption/target split

### Governing laws

- `SatisfiesSpinHalfBornRule` states the universal spin-one-half transition law
  `P(s₂ along b | s₁ along a) = (1 + s₁ s₂ (a · b))/2`, probability bounds,
  and complementarity. It quantifies over every preparation axis, measurement
  axis, and pair of outcomes; it does not contain this problem's angles,
  numerical probabilities, tolerance, or answer label.
- `SatisfiesSequentialAnalyzerSemantics` identifies each second-analyzer
  readout with the transition probability conditional on the branch selected
  at the first analyzer.

### Previous-part results

- None. The source report's `previous_parts` array is empty.

### Figure/data readouts

- `MatchesSternGerlachQuestion` records the intended quantum setup:
  `theta = 2 * pi / 3`, `phi = pi / 4`, selection of the positive first
  branch, and alignment of the second analyzer with positive `x`.
- `AnalyzerAngleReadouts` names scalar radian readouts. Transition
  probabilities and displayed probabilities are explicitly documented as
  dimensionless real readouts.
- Direct inspection of `phyx_data/test_image/541.png` confirms that the
  supplied raster is unrelated relativity artwork. It shows frames `K` and
  `K'`, axes `x`, `y`, `x'`, and `y'`, a space station, spaceship, proton,
  asteroid, and right-pointing arrows labelled `v`, `u`, and `u'`.
  `MatchesSuppliedRelativityRaster` preserves those source facts separately and
  records that the raster is not a Stern--Gerlach apparatus.
- `displayedProbabilityPair` records all four printed answer pairs.
  `recordedDatasetAnswer = D` is retained only as source metadata and is not a
  premise of the theorem.

### Current target conclusions

- `specifiedDirection_dot_positiveX` concludes the geometric intermediate
  relation `n · x = sqrt 6 / 4`.
- `problem_phyx_mini_0541` concludes the exact probabilities
  `P(+x) = (4 + sqrt 6)/8` and `P(-x) = (4 - sqrt 6)/8`, their agreement with
  `0.806` and `0.194` at absolute tolerance `1/2000`, and that `D` is the
  unique matching displayed answer choice.

## Goal-faithfulness audit

The exact probabilities, decimal-approximation claims, and uniqueness of
choice D occur only in the main conclusion and in source-display metadata.
They do not occur in `SatisfiesSpinHalfBornRule`,
`SatisfiesSequentialAnalyzerSemantics`, `MatchesSternGerlachQuestion`, or
`MatchesSuppliedRelativityRaster`. The Born-rule premise is genuinely general
over axes and outcomes. The apparatus-semantics premise supplies only the
conditional-measurement interpretation. The unrelated raster contributes no
quantum law and cannot determine the answer. No local definition unfolds to
the current theorem conclusion.

The source/law/answer audit is consistent. In the adopted spherical-coordinate
convention,
`n_x = sin(2*pi/3) * cos(pi/4) = sqrt 6 / 4`; applying the general positive- and
negative-outcome Born rule gives the two exact target probabilities, whose
three-decimal readouts uniquely match D. The primary raster cannot independently
support this calculation, so its incompatible contents remain isolated as
source evidence.

## Declarations and blueprint correspondence

- Blueprint theorem `thm:physics:phyx_mini_0541:target` corresponds to
  `PhyXMiniProblems.ProblemPhyXMini0541.problem_phyx_mini_0541`.
- Blueprint lemma
  `lem:physics:phyx-mini-0541:phyxminiproblems-problemphyxmini0541-specifieddirection-dot-positivex`
  corresponds to `specifiedDirection_dot_positiveX`.
- The blueprint definition labels with the common prefix
  `def:physics:phyx-mini-0541:phyxminiproblems-problemphyxmini0541-` correspond
  respectively to these Lean declarations:

  - `spindirection` → `SpinDirection`
  - `spinoutcome` → `SpinOutcome`
  - `outcomesign` → `outcomeSign`
  - `spindirectiondot` → `spinDirectionDot`
  - `sphericalspindirection` → `sphericalSpinDirection`
  - `positivexdirection` → `positiveXDirection`
  - `analyzeranglereadouts` → `AnalyzerAngleReadouts`
  - `spinhalftransitionmodel` → `SpinHalfTransitionModel`
  - `sequentialsterngerlachexperiment` → `SequentialSternGerlachExperiment`
  - `satisfiesspinhalfbornrule` → `SatisfiesSpinHalfBornRule`
  - `satisfiessequentialanalyzersemantics` →
    `SatisfiesSequentialAnalyzerSemantics`
  - `matchessterngerlachquestion` → `MatchesSternGerlachQuestion`
  - `rasterframe` → `RasterFrame`
  - `rasterobject` → `RasterObject`
  - `rasteraxis` → `RasterAxis`
  - `rastervelocitysymbol` → `RasterVelocitySymbol`
  - `suppliedrelativityraster` → `SuppliedRelativityRaster`
  - `pointsalongpositivehorizontalaxis` → `PointsAlongPositiveHorizontalAxis`
  - `matchessuppliedrelativityraster` → `MatchesSuppliedRelativityRaster`
  - `answerchoice` → `AnswerChoice`
  - `displayedprobabilitypair` → `displayedProbabilityPair`
  - `recordeddatasetanswer` → `recordedDatasetAnswer`
  - `probabilityapproximatelyequal` → `ProbabilityApproximatelyEqual`
  - `matchesdisplayedchoicewithin` → `MatchesDisplayedChoiceWithin`
  - `isuniquematchinganswerchoice` → `IsUniqueMatchingAnswerChoice`

The theorem environment is ready for `\leanok`, but this lane did not edit the
blueprint because the iteration's explicit write permissions allow edits only
to the assigned Lean file and this result file.

## LeanExplore queries and candidates actually used

Every search in this iteration used `packages: ["Mathlib", "Physlib"]`.

- `Stern Gerlach spin one half Born transition probability Bloch sphere`
  returned `Metric.sphere` and unrelated near misses including
  `QuantumMechanics.angularMomentumOperatorSqr_apply_fun`; it returned no
  directional Stern--Gerlach transition law.
- `quantum state measurement probability inner product projector` returned
  generic inner-product declarations, not an indexed qubit measurement API.
- `EuclideanSpace unit vector norm inner product` returned
  `inner_self_eq_one_of_norm_eq_one`,
  `InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one`, and
  `EuclideanSpace.norm_single`, grounding the Euclidean unit-direction model.
- `BlochSphere blochPoint dot_blochPoint` did not return an accessible
  Bloch-sphere declaration.
- Exact-name searches for `EuclideanSpace`, `Metric.sphere`, `dotProduct`, and
  `QuantumMechanics.FiniteTarget` returned those declarations. Source/module
  lookups were then fetched only for these intended candidates.

The fetched results locate:

- `EuclideanSpace` in `Mathlib.Analysis.InnerProductSpace.PiL2`; its source
  explicitly provides the `EuclideanSpace ℝ (Fin n)` model and `!₂[...]`
  notation used in this file.
- `Metric.sphere` in `Mathlib.Topology.MetricSpace.Pseudo.Defs`.
- `dotProduct` in `Mathlib.Data.Matrix.Mul`.
- `QuantumMechanics.FiniteTarget` in
  `Physlib.QuantumMechanics.FiniteTarget`. Its source bundles a finite Hilbert
  space with a self-adjoint Hamiltonian, which is extra dynamical structure and
  does not state the static directional measurement law needed here.

## PhysLean/Mathlib names grounded

- Direct Mathlib import:
  `Mathlib.Analysis.InnerProductSpace.PiL2`.
- Physlib import and inspected near miss:
  `Physlib.QuantumMechanics.FiniteTarget` and
  `QuantumMechanics.FiniteTarget`.
- Mathlib declarations/types used in the model: `Metric.sphere`,
  `EuclideanSpace`, `dotProduct`, `Real.sin`, `Real.cos`, `Real.pi`,
  `Real.sqrt`, and real absolute value.

## Local abstractions introduced

- `SpinOutcome` preserves the two physical analyzer ports and their eigenvalue
  signs.
- `SpinHalfTransitionModel` and `SatisfiesSpinHalfBornRule` preserve the
  specialized directional transition law absent from the accessible library
  API.
- `SequentialSternGerlachExperiment` and
  `SatisfiesSequentialAnalyzerSemantics` keep an apparatus readout distinct
  from the abstract law until an explicit premise relates them.
- `AnalyzerAngleReadouts` separates dimensionless radian readouts from the
  physical unit directions represented by points of `Metric.sphere`.
- The raster types preserve image labels, arrows, and spatial relations without
  confusing them with the quantum apparatus.
- The answer-choice and approximate-equality definitions preserve the finite
  multiple-choice claim and its stated decimal precision.

These abstractions do not collapse a physical primitive to a scalar alias:
directions are library unit-sphere points, outcomes are a finite physical type,
and real scalars are used only for named angle, coordinate, probability, and
image readouts.

## Grounding gaps

- The checked-out dependency contains
  `QuantumInfo.States.Pure.BlochSphere` with source definitions named
  `BlochSphere`, `BlochSphere.blochPoint`, and
  `BlochSphere.dot_blochPoint`. A real Lake/LSP snippet importing that module
  reports all three identifiers as unknown because the declarations are not
  exported by the module. The formalization therefore uses the accessible
  Mathlib `Metric.sphere`, `EuclideanSpace`, and `dotProduct` API.
- No indexed, importable Physlib declaration found in the searches states the
  conditional spin-one-half Stern--Gerlach Born law for two directions. The
  faithful universal local law predicate is therefore necessary.
- The requested `.archon/AGENTS.md` is absent from this checkout. The injected
  role and write-permission instructions and the available
  `.archon/prover-modes/physics-formalize.md` were followed.
- The prompt says `archon` is on `PATH`, but both requested DAG queries fail
  with `archon: command not found`. The chapter topology itself supplies the
  declaration dependencies needed for this target.
- No physics redraft is requested: the source/image mismatch is explicitly
  preserved, and the semantic model passed the prior review.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0541.lean` exits 0 in
  5.5 seconds after adding the direct Mathlib import.
- Lean LSP diagnostics report success, no failed dependencies, and only four
  expected `sorry` warnings: two unit-sphere membership proofs, the
  dot-product lemma, and the main target.

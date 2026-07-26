# Autoformalization result: `problem_phyx_mini_0650.lean`

## Assumption/target split

### Governing laws

- `SatisfiesRodComponentGeometry` states ordinary Euclidean component geometry.  In the moving observer's frame, the signed longitudinal and transverse readouts are `L cos θ` and `L sin θ`; in each frame, the squared length magnitude is the sum of the squared components.
- `SatisfiesRelativisticRodLengthTransformation.longitudinalLengthContraction` states the generic special-relativistic law `L_parallel = L0_parallel / γ(β)` in every selected length unit.
- `SatisfiesRelativisticRodLengthTransformation.transverseLengthInvariant` states that a boost along the motion axis leaves the transverse rod component unchanged.
- `HasPhysicalObliqueRodParameters` supplies positive apparent and proper length magnitudes, a nonnegative subluminal speed fraction, and the first-quadrant sign conditions for the apparent components.  It gives no numerical proper length.

### Previous-part results

- None.  The source report's `previous_parts` list is empty.

### Figure/data readouts

- `MatchesProblemStatementReadouts` records the prose data only: apparent length `2.00 m`, apparent angle `30.0°`, and dimensionless relative speed `β = 199/200 = 0.995`.
- `MatchesObliqueRodScenario` assigns the proper-length measurement to the rod rest frame, the apparent measurement to the moving observer's frame, and the relative motion to the positive `x` direction.
- Inspection of the primary raster found that it contradicts the generated rod caption.  `SuppliedProbabilityDensityFigure` and `MatchesSuppliedImage650` therefore preserve what image 650 actually shows: an `x (cm)` horizontal axis, a `|ψ(x)|² (cm⁻¹)` vertical axis, the piecewise triangular readout `-x` on `[-1,0]` and `x` on `[0,1]`, zero exterior, endpoint drops, and no rod or observer-motion arrow.
- `AnswerChoice` and `displayedProperLengthMeters` retain the four printed values `12.1`, `17.4`, `11.5`, and `13.3` meters.  `recordedDatasetAnswer` records source metadata `.B` only.

### Current target conclusions

- `problem_phyx_mini_0650` concludes `MatchesDisplayedProperLengthChoice setup .B`: the independently modeled proper-length meter readout is within `0.05 m` of `17.4 m`, expressing rounding to the nearest tenth.

## Goal-faithfulness audit

- `properLength`, `properLongitudinalComponent`, and `properTransverseComponent` are independent dimensionful fields of `ObliqueRelativisticRodSetup`; none is defined from `17.4`, choice B, or the apparent measurements.
- No scenario, prose-readout, physical-domain, or actual-image premise asserts a numerical proper length or the rounded-choice target.
- The geometry premise is frame-generic Pythagorean/component geometry.  The relativity premise is the generic longitudinal/transverse transformation and contains neither the problem's numerical proper length nor any answer choice.
- `displayedProperLengthMeters` transcribes the multiple-choice list, but no premise asserts that the physical proper length matches one of those values.  Unfolding the answer metadata cannot prove the target.
- The actual raster data are intentionally independent and irrelevant to the rod calculation.  Encoding the source contradiction explicitly prevents the false caption from being smuggled in as figure evidence for the target.

## Declarations created and blueprint labels

- `problem_phyx_mini_0650` corresponds to `thm:physics:phyx_mini_0650:target`.
- Supporting declarations include dimensionful length/readout definitions; frame, direction, plot-label, plot-feature, unit-label, and answer-choice types; `SuppliedProbabilityDensityFigure`; `ObliqueRelativisticRodSetup`; scenario/image/readout/physical-domain structures; the component-geometry and relativistic-transformation law structures; and displayed-choice metadata.
- The blueprint chapter was not edited because the explicit prover write permissions restrict this lane to the assigned Lean file and task-result file.  After review, the plan agent should add `\lean{PhyXMiniProblems.ProblemPhyXMini0650.problem_phyx_mini_0650}` and `\leanok` to the target environment.

## LeanExplore queries/candidates actually used

- Natural-language query `special relativity Lorentz factor length contraction proper length` and likely-name query `lorentzFactor` found `LorentzGroup.γ` (id 391166).  Its fetched source is `def γ (β : ℝ) : ℝ := 1 / Real.sqrt (1 - β^2)` in `Physlib.Relativity.LorentzGroup.Boosts.Basic`; it is used by `lorentzFactor`.
- Query `physical dimensions SI length meter speed of light` found `DimSpeed.speedOfLight` (id 394486), `UnitChoices.SI` (id 394270), `UnitChoices.SI_length` (id 394271), `Dimension.L𝓭` (id 394324), and `LengthUnit` (id 393137).  Fetched source confirms that `DimSpeed.speedOfLight` is the exact dimensionful `299792458 m/s` constant and that `LengthUnit` is a positive unit scale.
- Queries `DimLength oneMeter dimensional length` and `WithDim length quantity meters` found the Physlib `Dimensionful`/`WithDim` infrastructure and `Dimension.L𝓭`, used for nonnegative length magnitudes and signed displacement components instead of scalar aliases.
- Likely-name query `LengthUnit.centimeters` found `LengthUnit.centimeters` (id 393160).  Its fetched source defines the unit as `10⁻²` meters; it is used to type the actual image's horizontal-axis unit.
- Queries `DimAngle degree radians` and `Real.Angle quotient radians cosine sine` found `Real.Angle` (id 146415), `Real.Angle.coe` (id 146418), `Real.Angle.sin` (id 146462), and `Real.Angle.cos` (id 146465) in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.  Their fetched sources ground `angleOfDegrees` and the component equations.

## PhysLean/Mathlib names grounded

- Mathlib: `Real.Angle`, `Real.Angle.coe`, `Real.Angle.sin`, `Real.Angle.cos`, `Real.pi`, and `NNReal`.
- PhysLean/Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `LengthUnit`, `LengthUnit.meters`, `LengthUnit.centimeters`, `UnitChoices.SI`, `DimSpeed`, `DimSpeed.speedOfLight`, and `LorentzGroup.γ`.

## Local abstractions introduced

- `LengthMagnitude` and `SignedLength` use Physlib's dimensionful unit machinery.  They distinguish a nonnegative physical magnitude from signed longitudinal/transverse displacement components without collapsing either to `ℝ`.
- `ObliqueRelativisticRodSetup` is the smallest aggregate that keeps the two frames, the physical speed, the two independent length magnitudes, four independent components, and the measured angle separate.
- `SatisfiesRelativisticRodLengthTransformation` is a local governing-law interface because the search found a Lorentz factor and Lorentz boosts but no ready-made theorem for longitudinal contraction of an arbitrarily oriented finite rod.
- `SuppliedProbabilityDensityFigure` is an explicit scalar plot-readout abstraction for the mismatched image.  It does not pretend that the quantum-mechanical plot is a rod diagram or use its data in the rod physics.

## Grounding gaps and redraft requests

- LeanExplore returned `Lorentz.coCoContract`, but that declaration contracts Lorentz tensor indices and is unrelated to physical length contraction.  No ready-made Physlib oblique-rod length-contraction API was found, so the faithful generic component-law structure was introduced locally.
- Source redraft requested: `phyx_data/test_image/650.png` is a triangular wavefunction-density plot, while the blueprint prose and generated caption describe a `2.00 m` rod at `30.0°` with an observer-motion arrow.  Either the image path or the caption/scenario association should be corrected.  This formalization preserves both the prose model and the actual raster evidence without conflating them.
- The requested `.archon/AGENTS.md` is absent.  `.archon/prover-modes/physics-formalize.md` and `.archon/PROGRESS.md` were read as the available role/state documents.
- The prompt advertised `archon dag-query`, but `archon` is not installed on this runner's `PATH`; no dependency-graph data could be retrieved.
- The assigned Lean file did not exist initially, so it contained no file-specific `/- USER: ... -/` comments to apply.

## Verification

- `archon-lean-lsp` diagnostics reported no errors and exactly one expected `declaration uses sorry` warning, for the target theorem.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0650.lean` exited with code 0 and only that expected warning.

## Iteration 018 prover result

- Closed `PhyXMiniProblems.ProblemPhyXMini0650.problem_phyx_mini_0650` without changing its signature.
- The proof evaluates the observer-frame components at \(30^\circ\), uses
  `LorentzGroup.γ_sq` at \(\beta = 199/200\), applies longitudinal contraction
  and transverse invariance, and derives the exact meter-readout identity
  \(L_0^2 = 120399/399\).
- Positivity of the proper length and exact rational square comparisons give
  \(17.35 < L_0 < 17.45\), which proves the half-tenth tolerance for choice B.
- `hScenario` and `hImage` are intentionally unused in the numeric derivation;
  they preserve the frame and mismatched-raster evidence in the theorem
  contract, while the conclusion follows from the readouts, physical-domain,
  geometry, and relativity hypotheses.
- No `sorry`, `admit`, new axiom, `sorryAx`, or `native_decide` remains in the
  assigned Lean file.

## Final verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0650.lean` exits 0. Its only
  messages are the expected unused-variable linter warnings for `hScenario` and
  `hImage`.
- Root `lake build` exits 0 with `Build completed successfully (4 jobs)`.
- The project has no per-module Lake target named
  `PhyXMiniProblems.problem_phyx_mini_0650`; attempting that target reports
  `unknown target`, so direct Lean compilation plus the successful root build
  provide the file- and project-level checks.

## Blueprint readiness

- The target theorem is proof-closed and ready for `\leanok`. The blueprint was
  not edited because the prover permissions restrict writes to this assigned
  Lean file and task-result file; the run's canonical `AGENTS.md` also assigns
  `\leanok` synchronization to the loop rather than prover lanes.

## Redraft needed

- No Lean theorem redraft is needed. The separate source image/caption mismatch
  remains the source-data redraft issue documented above.

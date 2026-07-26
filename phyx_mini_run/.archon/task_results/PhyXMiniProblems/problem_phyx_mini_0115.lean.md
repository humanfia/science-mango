# Iteration 016 prover retry result: `problem_phyx_mini_0115.lean`

## Current disposition

- No Lean edit was made. The assigned file is already proof-complete, its
  frozen declarations are unchanged, and both earlier proof reviews explicitly
  state that no Lean repair is indicated.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0115.lean` again completed
  with exit code 0. Lean LSP diagnostics contain no errors and only the expected
  unused-variable warning for the frozen `aperture` applicability hypothesis.
- `lean_verify` for
  `PhyXMiniProblems.ProblemPhyXMini0115.problem_phyx_mini_0115` reports no
  suspicious source patterns and only the standard dependencies `propext`,
  `Classical.choice`, and `Quot.sound`.
- There are no remaining `sorry`, `admit`, `sorryAx`, `native_decide`, or local
  `axiom` occurrences.
- The reviewed retry remains `partial` solely because the blueprint prose
  describes exact finite-scale endpoint laws and an exact physical image,
  whereas the frozen Lean contract uses a five-field near-axis
  limit/derivative/little-o model and proves the leading paraxial image length.
  Prover permissions explicitly forbid editing the blueprint; the plan/review
  stage must make that prose-only synchronization.
- All four proof declarations remain ready for deterministic `\leanok`
  synchronization.

## Outcome

- Proof-complete. The assigned Lean file contains no `sorry`, `admit`,
  `sorryAx`, `native_decide`, or local `axiom`.
- No Lean edit was needed in iteration 015. The iteration-014 proof bodies
  already close all four declarations honestly:
  `objectEndpointReadouts_exact`, `imageEndpointReadouts_exact`,
  `imageLengthInCentimeters_exact`, and `problem_phyx_mini_0115`.
- The mandatory retry arose only because the blueprint prose is stale. The
  iteration-014 reviewer explicitly found that the Lean proof compiles and is
  faithful to its frozen contract, and stated that no Lean proof repair is
  indicated.

## Proof audit

- `objectEndpointReadouts_exact` derives the endpoint object distances and
  heights from the midpoint relations, the 16 cm pencil length, and
  `sin (π/4) = cos (π/4) = √2/2`.
- `imageEndpointReadouts_exact` derives the homogeneous Gaussian equation by
  uniqueness of the limit of the exact axial response.
- The same lemma derives the leading signed-magnification equation from the
  transverse derivative and the two little-o residual statements. It then
  solves the four endpoint image readouts using the real-image branch
  hypotheses.
- `imageLengthInCentimeters_exact` expands the Euclidean separation of the
  two leading paraxial endpoint images and proves
  `3200 * Real.sqrt 10 / 593`.
- `problem_phyx_mini_0115` proves the nearest-tenth interval for 17.1 cm and,
  by exhaustive answer-choice analysis, that A is uniquely closest.
- The unused `aperture` hypothesis is a frozen physical applicability
  condition. It is not used as a proof shortcut and must not be removed or
  renamed.

## Assumption/target split

### Governing laws

- `SatisfiesParaxialThinLensLaws` supplies the exact-response axial limit,
  vanishing Gaussian residual, on-axis transverse response, transverse
  derivative, and little-o signed-magnification residual.
- `HasRealEndpointImages` supplies the positive focal length, beyond-focal
  endpoint branch, and positive leading image distances.
- `HasAdequateParaxialAperture` records the paraxial regime and adequate
  physical aperture.

### Previous-part results

- None. `reports/phyx_mini/problem_phyx_mini_0115.source.json` has
  `"previous_parts": []`.

### Figure/data readouts

- The convex converging lens has focal length 20 cm.
- The pencil has length 16 cm, center object distance 45 cm, center height
  15 cm, and inclination `π/4`.
- The endpoint labels, midpoint relations, and directed axial/transverse
  components are recorded in `MatchesPencilLensFigure`.
- The displayed answer lengths are A 17.1 cm, B 18.2 cm, C 19.3 cm, and
  D 16.8 cm.

### Current target conclusions

- The exact endpoint readouts of the leading paraxial model.
- The leading paraxial image length `3200 * √10 / 593` cm.
- Its nearest-tenth agreement with 17.1 cm and unique selection of answer A.

## Goal-faithfulness audit

- No premise stores a solved endpoint coordinate, the radical image length,
  the nearest-tenth result, or the selected answer.
- `imageLengthInCentimeters` is only the Euclidean separation of independently
  modeled leading paraxial endpoint points.
- The proof derives the Gaussian and magnification equations from the local
  limit/derivative/little-o contract; it does not assume them as exact
  finite-scale physical laws.
- Physical positions, lengths, focal length, and aperture remain dimensionful.
  Real numbers are used only for centimeter coordinate readouts, angle/scale
  parameters, residuals, and dimensionless comparisons.

## Blueprint sync needed

- Original problem: `phyx_mini_0115`.
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0115.source.json`.
- Affected declaration:
  `PhyXMiniProblems.ProblemPhyXMini0115.problem_phyx_mini_0115` and its three
  supporting lemmas.
- The current blueprint still describes `TiltedPencilLensSetup` as merely
  storing endpoint images, describes `imageDistanceCm`, `imageHeightCm`, and
  `imageLengthInCentimeters` as exact physical-image readouts, and describes
  `SatisfiesParaxialThinLensLaws` as two exact endpoint equations. The Lean
  contract instead has an exact scale-dependent response family and a
  five-field near-axis limit/derivative/little-o contract, whose conclusion is
  the leading paraxial image length.
- The smallest faithful fix is prose-only: update those blueprint descriptions
  and the dependent lemma prose to say “leading paraxial,” and describe the
  five asymptotic fields. No Lean signature or proof-body change is needed.
- This prover did not edit the blueprint because the explicit write permissions
  restrict it to the assigned Lean file and this result file. All four proved
  declarations are ready for deterministic `\leanok` synchronization.

## Verification

- Lean LSP diagnostics: no errors; one expected unused-variable warning for
  the frozen `aperture` hypothesis.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0115.lean`: exit code 0,
  with only the same warning.
- Root `lake build`: successful (4 jobs).
- `lean_verify` for
  `PhyXMiniProblems.ProblemPhyXMini0115.problem_phyx_mini_0115`: no source-scan
  warnings; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- `archon` was not on this lane's `PATH`, so the project-local executable at
  `/root/proposal_for_physic/science-mango/.venv/bin/archon` was used. The
  target-node query reports one theorem node with `has_sorry: false`, eight
  direct blueprint dependencies, and zero remaining local/total proof effort.
  Its `proved: false` flag is marker-derived and agrees with the missing
  `\leanok`, not with the independently verified Lean proof state.
- The ancestor query completed with all 27 transitive dependency nodes and no
  graph error; every returned node has `has_sorry: false`.

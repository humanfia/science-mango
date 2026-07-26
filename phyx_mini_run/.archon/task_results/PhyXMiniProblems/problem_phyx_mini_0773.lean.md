# Prover result: `problem_phyx_mini_0773.lean`

## Outcome

Closed all five proof obligations without changing any declaration signature:

- `earthObservedMassKineticEnergy_eq_485`
- `earthObservedMassSpeed_squared_eq_194_over_3`
- `equalDrumEnergy_gives_equalMassSpeedSquared`
- `marsObservedMassSpeed_eq_sqrt_194_over_3`
- `marsMassSpeedWhenDrumHas250J_matches_recordedAnswerB`

The Earth energy balance uses the zero release kinetic energies and the
readouts `m = 15 kg`, `g = 9.8 m/s²`, `h = 5 m`, and
`K_drum = 250 J` to derive `K_mass = 485 J`.  The translational
kinetic-energy law then gives `v_earth² = 194/3`.

For two trials of the shared apparatus, positivity of the drum inertia permits
cancellation in the rotational kinetic-energy equations.  Equal observed drum
energies therefore give equal angular-speed squares, and the no-slip equations
give equal attached-mass speed squares.  The nonnegative `NNReal` speed readout
selects the positive square root, so the Mars speed is exactly
`sqrt (194/3)`.  Exact rational square comparisons prove that this value lies
in the nearest-hundredth interval for `8.04 m/s`, hence it selects recorded
choice B.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0773.lean`: exit code 0
  with no diagnostics.
- Source scan found no remaining `sorry`, `admit`, added `axiom`,
  `native_decide`, or `sorryAx`-style escape hatch.

## Blueprint status

The proof environments for the five declarations above are ready for
deterministic `\leanok` synchronization.  The blueprint was not edited because
the prover role's explicit write permissions restrict this lane to the
assigned Lean file and this result file.

## Redraft needed

None.

## Infrastructure note

The run-local `.archon/AGENTS.md` was absent.  The canonical copy in
`phyx_mini_archives/20260722-review3-rerun/.archon/AGENTS.md` and the run-local
`.archon/prover-modes/physics.md` were read instead.  No dependency-graph lemma
was needed for this self-contained algebraic proof.

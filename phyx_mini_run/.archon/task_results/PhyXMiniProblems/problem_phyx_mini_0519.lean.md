# Prover result: `problem_phyx_mini_0519.lean`

## Outcome

- Closed `emittedPhotonWavelengthN4ToN2_roundsTo378Nanometers` with no remaining `sorry`.
- Preserved the theorem signature and all physical hypotheses unchanged.
- No redraft is needed.

## Proof

The proof specializes the uniform photon energy--wavelength law to the
transitions `n4 → n1`, `n2 → n1`, and `n4 → n2`.  Rewriting the first two laws
with the measured diagram wavelengths `75.63 nm` and `94.54 nm` determines the
requested level gap relative to the common `h c` factor:

`35750301 * (E₄ - E₂) = 94550 * h c`.

Strict level ordering supplies `0 < E₄ - E₂`, so the third transition law can
be cancelled honestly to obtain the exact wavelength

`λ₄₂ = 35750301 / 94550 nm ≈ 378.1100053 nm`.

`norm_num` then verifies
`377.5 ≤ λ₄₂ < 378.5`, which is precisely the target rounding predicate.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0519.lean` exited with code
  `0`; its only diagnostics are unused-variable lints for the scenario and
  ionization-data hypotheses.
- Source scan found no `sorry`, `admit`, introduced `axiom`, or `sorryAx`.
- `lean_verify` reports only the standard trusted axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious-source warnings.

## Blueprint synchronization

The theorem's blueprint environment is ready for `\leanok`.  I did not edit
the chapter because this prover lane explicitly permits writes only to the
assigned Lean file and this task-result file; the synchronization agent should
add the marker.

## Workspace note

`.archon/AGENTS.md` is absent in this workspace.  I followed the role contract
provided in the task prompt together with `.archon/PROGRESS.md`, the physics
blueprint chapter, the linked source report, and `references/summary.md`.

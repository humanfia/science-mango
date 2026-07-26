# Prover result: `problem_phyx_mini_0371.lean`

## Status

Complete. All three `sorry` placeholders were replaced with sound proofs, and
the assigned Lean file compiles.

## Declarations proved

- `mole_amount_from_stated_mass` rewrites the governing mass-to-moles law with
  the supplied `0.10 g` sample mass and `4 g/mol` helium molar mass, obtaining
  exactly `1/40 mol`.
- `initial_temperature_in_kelvin_from_stated_data` specializes the ideal-gas
  law at state `1`, converts the bitmap readout `1000 cm³` to `1 L`, and
  substitutes `p₁ = 1 atm`, `n = 1/40 mol`, and
  `R = 82057/1000000 L·atm/(mol·K)`. Linear rational arithmetic then yields
  `T₁ = 40000000/82057 K`.
- `problem_phyx_mini_0371` derives the Celsius readout by its defining
  `273.15` offset and checks all four answer constructors by exact rational
  arithmetic, proving that none lies within half a degree of the computed
  temperature.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0371.lean` passed with no
  errors or warnings.
- A source scan found no `sorry`, `admit`, declared `axiom`, `sorryAx`,
  `native_decide`, or other proof escape.
- Only the three proof bodies after `:= by` were edited; declaration signatures
  and hypotheses were left unchanged.

## Blueprint synchronization

The two lemma environments and target theorem environment are ready for
`\leanok`. The blueprint was not edited because the active prover-stage write
permissions allow changes only to the assigned Lean file and this task-result
file.

## Project metadata note

The requested run-local `.archon/AGENTS.md` is absent. The available
`.archon/prover-modes/physics.md`, `.archon/PROGRESS.md`, the complete physics
blueprint chapter, the grounding log, and the linked source report were read
and followed. The advertised `archon` command is also absent from `PATH`; no
dependency-graph result was needed for these local algebraic proofs.

## Redraft needed

None.

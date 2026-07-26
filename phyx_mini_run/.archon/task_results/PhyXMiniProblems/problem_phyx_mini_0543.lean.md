# Autoformalization result: `problem_phyx_mini_0543.lean`

## Retry-gate disposition

Iteration 003 addresses the exact review-gate reason: the gate requested a
genuine post-formalization report naming the searches and candidates actually
used, grounded library declarations, local abstractions, grounding gaps, and
the source/law/answer split. The rejection identified missing evidence only,
not a semantic defect. After re-reading the source report, inspecting image
`543.png`, auditing the revised Lean statement, and rerunning LeanExplore and
LSP checks, I found no semantic reason to change the public declarations.

The source says that an `x`-down spin-1/2 state evolves in a uniform field
`B₀ ẑ` and asks for the later `x`-up probability. The image visibly contains
an X analyzer with its lower branch selected, a central Z-labelled region with
an otherwise unexplained `42` glyph, a final X analyzer, and two blank outputs
marked `?`. The answer metadata records choice D, `sin²(ω₀ t / 2)`.

## Assumption/target split

### Governing laws

- `IsUniformAppliedFieldAlongZ` states that the full spacetime-dependent
  Physlib magnetic field is constant with value `B₀ ẑ`.
- `SatisfiesZeemanHamiltonian` states `H = -μ B₀ σ_z` in the spin-z basis and
  separately states the Larmor relation `ℏ ω₀ = 2 μ B₀`.
- `SatisfiesBornRuleForXSpinMeasurement` relates the independent probability
  observable to the norm square of the x-up transition amplitude and supplies
  probability bounds. It contains no sine formula.
- `HasPhysicalSpinPrecessionParameters` records positivity of the scalar SI
  readouts for field magnitude, magnetic-moment magnitude, and angular
  frequency.

### Previous-part results

- None. The source report has `previous_parts: []`.

### Figure/data readouts

- `MatchesSpinHalfPreparation` records the stated initial state `|-⟩_x`.
- `MatchesSuppliedSpinPrecessionFigure` transcribes the visible source beam,
  first X analyzer, selected lower/down branch, central Z region, raw glyph
  `42`, final X analyzer, upper/lower output branches, blank result boxes, and
  question marks.
- `SpinPrecessionExperiment` retains the full Physlib magnetic-field object,
  the finite quantum system, the initial state, coherent scalar SI readouts
  for `B₀`, `μ`, and `ω₀`, an independent probability observable, and the
  figure data. Elapsed-time arguments are explicitly named in seconds.
- The glyph `42` is deliberately only `Option Nat`: neither the image nor the
  source assigns it a unit or governing physical role.

### Current target conclusions

- `transitionAmplitudeToXUp` derives
  `⟪+x|U(t)|-x⟫ = i sin(ω₀ t / 2)` from preparation and Zeeman dynamics.
- `probabilityOfMeasuringSpinXUpAfterTime` derives, for every nonnegative
  elapsed time, `P(x-up) = sin²(ω₀ t / 2)` and identifies it with displayed
  choice D.

## Goal-faithfulness audit

The requested probability does not occur in `SpinPrecessionExperiment` or any
premise field. The probability function is independent experiment data.
Born's rule stops at a squared inner product, while the Zeeman premise stops at
the Hamiltonian and Larmor relations. The sine amplitude is a derived lemma
with a `by sorry` body, and the sine-squared probability remains in the main
theorem conclusion.

`displayedProbability` faithfully transcribes all four source choices. Its D
branch unfolds to the displayed sine-squared expression, but it never equates
that expression to the experiment's probability; the theorem's first
conjunct remains the substantive physical result. Thus the second conjunct
records answer-choice identification without making the physics true by
definition.

The full field, `B₀`, `μ`, preparation apparatus, and image glyph remain in the
model even where they disappear from the final closed form. The spin state is
Physlib's finite Hilbert-space object and the applied field is Physlib's
magnetic-field object, rather than either primitive being collapsed to `ℝ`.

## Declarations and blueprint labels

The delivered file contains the following declaration-to-label mapping:

| Lean declaration | Blueprint label |
|---|---|
| `SpinHalfState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinhalfstate` |
| `spinZBasis` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinzbasis` |
| `spinZUpState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinzupstate` |
| `spinZDownState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinzdownstate` |
| `spinXUpState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinxupstate` |
| `spinXDownState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinxdownstate` |
| `zDirection` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-zdirection` |
| `SpinAxis` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinaxis` |
| `SpinOutcome` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinoutcome` |
| `FigureBranchPosition` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-figurebranchposition` |
| `SpinPrecessionFigure` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinprecessionfigure` |
| `SpinPrecessionExperiment` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-spinprecessionexperiment` |
| `evolvedState` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-evolvedstate` |
| `MatchesSpinHalfPreparation` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-matchesspinhalfpreparation` |
| `IsUniformAppliedFieldAlongZ` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-isuniformappliedfieldalongz` |
| `MatchesSuppliedSpinPrecessionFigure` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-matchessuppliedspinprecessionfigure` |
| `HasPhysicalSpinPrecessionParameters` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-hasphysicalspinprecessionparameters` |
| `SatisfiesZeemanHamiltonian` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-satisfieszeemanhamiltonian` |
| `SatisfiesBornRuleForXSpinMeasurement` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-satisfiesbornruleforxspinmeasurement` |
| `AnswerChoice` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-answerchoice` |
| `halfLarmorPhase` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-halflarmorphase` |
| `displayedProbability` | `def:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-displayedprobability` |
| `transitionAmplitudeToXUp` | `lem:physics:phyx-mini-0543:phyxminiproblems-problemphyxmini0543-transitionamplitudetoxup` |
| `probabilityOfMeasuringSpinXUpAfterTime` | `thm:physics:phyx_mini_0543:target` |

## LeanExplore queries and candidates actually used

Every search in this pass used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `finite-dimensional Hilbert space quantum state
  Hamiltonian time evolution` returned and grounded
  `QuantumMechanics.FiniteHilbertSpace`, `QuantumMechanics.FiniteTarget`, and
  `QuantumMechanics.FiniteTarget.timeEvolution`.
- Likely-name query `QuantumMechanics.FiniteHilbertSpace FiniteTarget
  timeEvolution` independently confirmed the state-space and evolution APIs.
- Query `PauliMatrix.pauliMatrix sigma z spin one half` returned and grounded
  `PauliMatrix.pauliMatrix`; its `Sum.inr 2` source branch is
  `!![1, 0; 0, -1]`.
- Query `Electromagnetism.MagneticField uniform magnetic field` returned and
  grounded `Electromagnetism.MagneticField`. No result supplied a directly
  applicable uniform-`B₀ ẑ` predicate.
- Query `Born rule quantum measurement probability squared inner product
  transition amplitude` returned only generic inner-product/probability
  declarations, not a finite-target Born-measurement interface.
- Query `Stern Gerlach spin one half x eigenstate spin measurement` returned
  no relevant apparatus or spin-x eigenstate declaration.
- Query `Constants.ℏ reduced Planck constant` returned and grounded
  `Constants.ℏ`.

For every retained Physlib candidate I fetched its source, module, and
docstring. The retained candidate IDs were `390241`, `390170`, `390171`,
`391341`, `385560`, and `390795`, respectively.

## Physlib/Mathlib names grounded

- `QuantumMechanics.FiniteHilbertSpace (Fin 2)` is the complex
  finite-dimensional Hilbert space used for the two spin components.
- `QuantumMechanics.FiniteTarget SpinHalfState 2` packages a self-adjoint
  Hamiltonian, and `QuantumMechanics.FiniteTarget.timeEvolution` is defined as
  `exp (-(i t / ℏ) H)`.
- `Electromagnetism.MagneticField 3` has the source type
  `Time → Space 3 → EuclideanSpace ℝ (Fin 3)`.
- `PauliMatrix.pauliMatrix (Sum.inr (2 : Fin 3))` is the diagonal sigma-z
  matrix.
- `Constants.ℏ` is the positive reduced Planck constant in J.s.
- Mathlib supplies `Module.Basis`, `EuclideanSpace`, `inner`,
  `Complex.normSq`, and the real trigonometric functions used in the state,
  amplitude, and answer formulas.

The grounded Physlib modules are
`Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic`,
`Physlib.QuantumMechanics.FiniteTarget`,
`Physlib.Relativity.PauliMatrices.Basic`,
`Physlib.Electromagnetism.Basic`, and
`Physlib.QuantumMechanics.PlanckConstant`.

## Local abstractions introduced

- `SpinPrecessionFigure` and its finite label types preserve the supplied
  apparatus geometry and raw labels, for which no matching library apparatus
  type was found.
- `SpinPrecessionExperiment` packages the library quantum system and full
  magnetic field with dimensionally named scalar readouts and the independent
  probability observable.
- The premise structures isolate preparation, uniform-field geometry, image
  transcription, positivity, Zeeman dynamics, and Born measurement so their
  physical roles remain explicit and separate from the conclusion.
- `AnswerChoice` and `displayedProbability` preserve all four printed options,
  including the unbounded tangent and cotangent distractors.

## Grounding gaps and redraft requests

- No dedicated Stern--Gerlach apparatus, spin-1/2 x-eigenstate API, or
  finite-target Born-rule measurement interface was found, so the smallest
  role-preserving local abstractions were retained.
- The chapter exists and is marked `% archon:physics`, but its target proof is
  still an autoformalization instruction rather than the informal physical
  derivation requested from the plan stage. A later blueprint pass should add
  that derivation.
- The prompt asks for `\leanok` after formalization, but its explicit write
  permissions forbid editing blueprint chapters. No blueprint file was
  changed; marker synchronization remains for an authorized blueprint pass.
- The advertised `archon dag-query` command was attempted for the target node,
  but `archon` is not available on this environment's `PATH`.
- The requested `.archon/AGENTS.md` is absent. I used the complete
  `.archon/prover-modes/physics-formalize.md` role instructions instead.

## Verification

`archon-lean-lsp` reports successful elaboration, no failed dependencies, and
only the two expected `declaration uses sorry` warnings at the derived
amplitude lemma and target theorem. The final command
`lake env lean PhyXMiniProblems/problem_phyx_mini_0543.lean` exits successfully
with exactly those same two warnings.

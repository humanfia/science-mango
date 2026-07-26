# Prover result: `problem_phyx_mini_0010.lean`

## Outcome

- Closed the sole `sorry` in
  `PhyXMiniProblems.ProblemPhyXMini0010.problem_phyx_mini_0010`.
- Kept the declaration signature and all physical definitions unchanged.
- No `sorry`, `admit`, `sorryAx`, or new axiom remains in the assigned file.

## Proof summary

- Substituted the figure readouts \(n_{\rm in}=n_{\rm out}=1\) and
  \(n_{\rm rod}=1.36=34/25\).
- Used the limiting internal angle
  \(\alpha=\arccos(25/34)\). The acute-branch trigonometric identity proves
  \((34/25)\sin\alpha=\sqrt{531/625}\), so
  \(\theta_{\max}=\arcsin(\sqrt{531/625})\) satisfies entry Snell refraction
  and the wall TIR threshold.
- For an arbitrary guided ray, the TIR inequality gives
  \(\cos\alpha\ge 25/34\). Comparing squares on the nonnegative acute branch
  yields \((34/25)\sin\alpha\le\sqrt{531/625}\); Snell's law and strict sine
  monotonicity then give \(\theta\le\theta_{\max}\).
- Certified the degree interval \([67.15,67.25]\) without an approximate
  premise. The proof uses rational square-root bounds, exact
  \(3\pi/8=67.5^\circ\) sine/cosine values, and `Real.sin_bound` /
  `Real.cos_bound` on the small residual angles.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0010.lean` — exit code 0
  (two style-linter warnings only).
- `lake build` — completed successfully.
- `lean_verify` reports only the standard trusted axioms `propext`,
  `Classical.choice`, and `Quot.sound`, with no suspicious source patterns.
- A direct source scan found no proof placeholders or axiom declarations.

## Blueprint marker

The theorem and its proof block for
`thm:physics:phyx_mini_0010:target` are ready for `\leanok`. The blueprint was
not edited because prover permissions reserve marker synchronization for the
post-prover phase.

## Redraft needed

None.

# Auto-Research Harness: Beat IBM's qLDPC Bicycle-Code SOTA

## Objective

Build an automated research harness that discovers quantum LDPC codes strictly better
than the state of the art: IBM's bivariate bicycle (BB) family — the [[144,12,12]]
"gross code" ([Bravyi et al., Nature 627, 778 (2024)](https://www.nature.com/articles/s41586-024-07107-7),
[arXiv:2308.07915](https://arxiv.org/abs/2308.07915)) — and the results of IBM's own
LLM-guided search harness ([arXiv:2606.02418](https://arxiv.org/abs/2606.02418),
[qiskit-community/qcode-discovery](https://github.com/qiskit-community/qcode-discovery):
~2×10⁵ candidates, ~140 h, ~$400; raised best CSS k from 16 → 54).

## The metric: k·d²/n at check weight w ≤ 6

One scalar from three integers — n (physical qubits), k (logical qubits), d (minimum
distance). It measures qubit-overhead advantage over the surface code: rotated surface
code = 1 ([Fowler et al., arXiv:1208.0928](https://arxiv.org/abs/1208.0928)); gross code
= 12·12²/144 = **12** — the "~10× fewer qubits" headline of the Nature paper.
**A win = a certified code with k·d²/n > 12 at w ≤ 6**, or a Pareto win (same score at
smaller n; higher k or d with the rest fixed). The w ≤ 6 constraint (check weight and
qubit degree) makes the metric non-gameable — dense random codes get good (n,k,d) but
are unbuildable — and matches IBM's hardware roadmap.

Why this metric satisfies the target-selection criteria:

1. **Recognized** — it is the figure of merit of the Nature paper and every follow-up;
   the SOTA table is actively contested (IBM, academic groups, LLM-search papers) — a
   living leaderboard with a named adversary, and any win doubles as "our harness beat
   IBM's harness."
2. **Clear** — one number from three integers; no noise model, decoder, or error bars.
3. **Easily verifiable** — n read off; k = exact GF(2) rank; d certified deterministically
   (pipeline below). Certificate ≈ two polynomials + a rerun script.
4. **Incremental** — a Pareto frontier, not one record: beat 12, match it at n < 144,
   push k at fixed d, fill gaps between known BB codes [[72,12,6]], [[90,8,10]],
   [[108,8,10]], [[144,12,12]], [[288,12,18]]
   ([ECZoo entry](https://errorcorrectionzoo.org/c/qcga)).
5. **Impact** — certified k·d²/n > 12 at w ≤ 6 means fewer physical qubits for equal
   protection on IBM-style hardware; publishable at the tier where the gross code landed.

*Caveat:* k·d²/n is a proxy for logical error rate (ignores decoder performance). Hence
the secondary, reported-but-never-scored metric: circuit-level LER via
[stim](https://github.com/quantumlib/Stim) + BP-OSD
([`ldpc`](https://github.com/quantumgizmos/ldpc),
[Roffe et al., PRResearch 2, 043423 (2020)](https://journals.aps.org/prresearch/abstract/10.1103/PhysRevResearch.2.043423))
— reproducible by rerun (published circuits + seeds) but stochastic.

## Verification: how arbitrary agent constructions are scored

**Principle:** never trust agent claims. Every construction reduces to binary
parity-check matrices (Hx, Hz) over GF(2); a frozen, versioned verifier in a separate
process recomputes everything. Fitness = verifier output only.

| Tier | Cost | What | How |
|---|---|---|---|
| 0. Validity | ms | It's a real w ≤ 6 qLDPC code | `Hx·Hzᵀ = 0 (mod 2)`; row/column weights ≤ 6; Tanner graph connected (kills direct-sum cheats — IBM's [[288,24,12]] "find" was two independent gross codes) |
| 1. n, k | ms, exact | Deterministic parameters | k = n − rank₂(Hx) − rank₂(Hz) (`galois` / `ldpc.mod2`) |
| 2. Screen d | sec–min, probabilistic | Cheap rejection only — **never scores** | [QDistRnd](https://github.com/QEC-pages/QDistRnd) randomized search → true upper bound d̂ (it exhibits a real logical); discard if k·d̂²/n ≤ SOTA |
| 3. Certify d | min–hrs, deterministic | **The only tier that scores** | Split certificate below |

**Tier 3 split certificate** (asymmetric cost — this is what makes it practical):

- *Upper bound (ms to verify):* a witness vector w with `Hx·w = 0`, `w ∉ rowspace(Hz)`,
  `|w| = d`. Poly-time checks; any skeptic verifies instantly.
- *Lower bound (the expensive half):* prove no lighter logical exists via 2k integer
  programs — for each logical representative Lᵢ:
  `min Σvⱼ s.t. Hx·v = 2u, ⟨Lᵢ,v⟩ = 1+2t, v ∈ {0,1}ⁿ`; d = min over both sectors.
  IBM's own certification method for d = 12 (Methods of
  [arXiv:2308.07915](https://arxiv.org/abs/2308.07915)). Solvers: Gurobi/CPLEX or
  CP-SAT/HiGHS; the branch-and-bound optimality proof is the rerunnable certificate.
  BB codes' transitive cyclic symmetry lets one support position be fixed WLOG,
  keeping n ≈ 150–300 tractable. Methods survey:
  [arXiv:2603.22532](https://arxiv.org/abs/2603.22532).

**Anti-gaming rules:** dedup against the known-code registry; known-answer gate — the
pipeline must independently re-certify [[144,12,12]], [[72,12,6]], [[90,8,10]] before
any new claim counts; no stochastic quantity ever enters the score. Each win exports a
JSON certificate (ansatz polynomials, matrix hashes, witness, solver logs) + one-command
`verify.py`.

## Milestones

1. **Reproduce the baseline** — clone qcode-discovery; re-certify IBM's published codes
   end-to-end through our screen → certify pipeline. Proves the harness before any hunt.
2. **Attack the open fronts** — IBM optimized k; target d and k·d²/n fronts and
   under-explored block sizes with our own LLM-guided evolutionary loop.
3. **Expand the ansatz (stretch)** — multivariate/multicycle
   ([arXiv:2601.18879](https://arxiv.org/abs/2601.18879)), structured concept evolution
   ([arXiv:2606.24808](https://arxiv.org/abs/2606.24808)), BB algebra
   ([arXiv:2606.08771](https://arxiv.org/abs/2606.08771)), lifted-product neighborhoods.

## Additional references

- Google Quantum AI, surface code below threshold —
  [Nature 638 (2025)](https://www.nature.com/articles/s41586-024-08449-y) /
  [arXiv:2408.13687](https://arxiv.org/abs/2408.13687)
- Matching decoder for BB codes — [arXiv:2602.22770](https://arxiv.org/abs/2602.22770)
- qLDPC primer — [postquantum.com](https://postquantum.com/quantum-computing/quantum-low-density-parity-check-qldpc-codes/)

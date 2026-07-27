# IPhO 2026 formalization results

Snapshot date: 2026-07-27 (UTC)

| Metric | Result |
|---|---:|
| Original selected targets | 28 |
| Active theory targets | 22 |
| User-skipped experimental targets | 6 |
| Theory formalization/semantic Review passed | 22/22 (100%) |
| Theory proof Review solved | 22/22 (100%) |
| Theory zero-`sorry` files | 22/22 (100%) |
| Experimental `sorry` count retained | 17 |
| Final `lake build` | Passed |

The six E1 targets are explicitly `skipped_experimental`; they are neither
passes nor failures. Their partial formalizations are retained for future work.

## Proof-to-formalization routing exercised

- `1_C_1`: proof Review found a false helper contract for signed photon
  momentum. The pipeline routed it to formalization, added physical validity,
  re-reviewed the statement, and then completed the proof.
- `2_B_1`: proof Review found that an all-angle coefficient identity assumed
  the requested answer. The pipeline removed that premise, derived the radius
  equation from maximal-ray tangency, re-reviewed it, and proved the result.

## Reproducibility

- Pipeline source commit: `23cfed452cf4f3ae9f7fbcdd3b520c41f48204f9`
- Final inner run commit: `73f6821c15cad1a0382a4b93e25aa10d29cabae5`
- 28-row input SHA-256: `da9506ae22ffb831cf0085a6e1fb6819484a31f2303f8701c9f05afa88c82f6a`
- Successful checkpoint: iteration 5
- Summed iteration wall time to checkpoint: 7307 s

See `COMPARISON.md` and `comparison.json` for the old/new comparison.

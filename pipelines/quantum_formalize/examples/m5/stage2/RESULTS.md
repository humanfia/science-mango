# Stage 2 results — 2026-09-15

All eight frozen section-5 targets passed Lean acceptance, followed by assembled proof compilation and axiom checks. The shared project fingerprint remained unchanged. Together with stage 1, 17 individual lemmas are now accepted; this is not a claim that complete M5 has been formalized.

| Node | Attempts |
|---|---:|
| bounded_progression | 1 |
| bounded_source_order | 1 |
| cyclic_as_sub | 1 |
| modulus_multiple | 2 |
| progression_difference | 1 |
| progression_congruence | 1 |
| common_divisors_lift | 1 |
| triple_divisors_lift | 1 |

The final polynomial result is: if gcd(a,b) divides M_E, then for every polynomial D, D divides all of a,b,M_(T+jE) iff D divides all of a,b,M_T. This quantifies over full polynomial divisors, retaining repeated-factor information. It is not yet a complete physical-code lift theorem: support feasibility, connectivity repair and the global counting law remain separate obligations.

The numerical branch proves the progression meets [L,L+E), then derives the stated birth-bound inequality under explicit hypotheses on E. It does not establish those period-size hypotheses or create the physical support pair.

[Assembled proof](experiment/AcceptedExperiment.lean), [receipt](experiment/result.json), and [DAG status](experiment/GRAPH.md) are archived with frozen specs, model drafts, retrievals, compiler diagnostics and hashes. Replay with the matching Lean project files in lean/.

Controller code for this run was a044a05e. During this run, a separate retrieval improvement was tested for future launches: preserve successful original Mathlib results when substituting a Physlib fallback. It does not retroactively change this run's receipts or targets.

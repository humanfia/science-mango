# Published-volume generalized-toric/BB ansatz v3

Status: implemented and preregistered; not launched.  This representation is
checkpoint-incompatible with the published-volume v2 search.

## Scientific change

The evolved block now proposes the complete pair of BB supports.  The
immutable wrapper does not append `1+x`, `1+y`, a constant, a third monomial,
or any literature construction.  The finite support domain contains the
ordered splits `2+4`, `4+2`, `2+3`, `3+2`, `2+2`, and `3+3`, with combined
weight at most six.  The wrapper validates, reduces, deduplicates, and expands
those supports over every allowed HNF/twist cell, but does not repair a weak
proposal by injecting defaults.

The search program is
`evolve/seed_solution_twisted_torus_ansatz_v3.py`; its model prompt and MAP
Elites geometry are in `evolve/config_twisted_torus_ansatz_v3.yaml`.  The
representation identity is
`css-bb-twisted-torus-published-volume-ansatz-generator-v3`.

Published anchors are hidden during search.  Only
`scripts/verify_blind_ansatz_v3_calibration.py` may compare a sealed candidate
log with the anchor manifest.  A blind match earns calibration credit and
zero fitness, novelty, search-coverage, or discovery credit.
`evaluation/ansatz_v3_program_guard.py` validates every evolved v3 program
before import: the mutable block cannot import, perform filesystem/network
I/O, introspect Python internals, or add top-level execution.  Thus the blind
boundary is enforced by evaluator code as well as stated in the prompt.

## Formal audit allocation

`configs/twisted_torus_ansatz_v3.formal_audit_quota.v1.json` fixes 72 fresh
audit slots: eight slots for each published target volume 105, 124, 126, 127,
132, 147, and 170, plus four slots for controls 36, 45, 54, and 144.  Volumes
127 and 132 are mandatory.  Within a volume, selection maximizes new
`lattice-q`, algebraic-mechanism, and support-split strata.  A missing volume
leaves a durable unfilled slot; it is never silently reassigned.

BP/OSD, decoder estimates, and logical upper-bound witnesses cannot provide
positive promotion.  Replayed X/Z witnesses may produce
`evaluation/ansatz_witness_fingerprint.py` fingerprints for negative mutation
feedback only.  Positive distance progress still requires replayed two-sector
UNSAT evidence or an exact certificate.

## Dual-track response to the ladder diagnostic

The observed `LB >= 9` signal means “retain the generalized-toric/BB family,”
not “keep the old fixed-anchor representation unchanged.”  The preregistered
response in `configs/twisted_torus_ansatz_v3.dual_track.v1.json` is two
evidence-isolated tracks:

1. Prepare the fresh full-support ansatz-v3 run with no inherited checkpoint,
   diagnostic candidate, or diagnostic proof score.
2. Separately resume every diagnostic candidate that still lacks a trusted
   upper bound.  At most eight are active in the first batch; every remainder
   is retained in the same self-hashed plan as `QUEUED_DURABLE`.  Replayed
   `LB >= 9` is a priority signal, never an admission filter.  Each candidate
   resumes at its first UNKNOWN ladder rung: a replay-bound UNSAT sector is
   retained and only UNKNOWN sectors are retried there; both sectors are
   required again at every higher rung.  UNKNOWN remains unresolved/fail-open.

If a replayed candidate actually reaches the target lower bound, the planner
gives it priority route `independent_exact_certificate` and holds the richer
ansatz at `PREPARED_HELD_FOR_CERTIFICATE_DECISION`.  An UNKNOWN at the target
rung is not such a survivor: it remains an open checkpoint retry and leaves
the fresh ansatz `READY_NOT_LAUNCHED`.

`evaluation/ansatz_v3_dual_track.py` replays the diagnostic contract, initial
`d >= 5` proof, every X/Z rung, result derivations, file identities, and the
machine decision.  It then binds each survivor to the diagnostic contract,
decision, selected row, construction digest, and result hashes.  Planning
does not start either track.  The resulting manifest requires different run
IDs, artifact roots, checkpoints, and ledgers for fresh search and deep proof:

```bash
python -B scripts/build_ansatz_v3_dual_track_plan.py \
  /absolute/path/to/completed-diagnostic \
  /absolute/path/to/new-dual-track-plan.json
```

The diagnostic itself must be the installed, published implementation at Git
commit `eb4347518fe801057783dd43051bd5266f69e0a8`.  A plan is produced only
after `results.jsonl` and `decision.json` are complete and replayable.

The plan is not directly consumable by the existing Stage-3 ranked-pool CLI:
that CLI cannot express a sector-specific UNKNOWN checkpoint or a multi-rung
resume.  A dedicated provenance-checking resumable-sector driver is therefore
a launch blocker, recorded in the plan itself.  Treating the plan as ordinary
`campaign_audit.status=UNRESOLVED` input and jumping straight to the target
rung is forbidden.

## Template and family boundary

`configs/campaign_templates.ansatz_v3.json` is the installed schema-v2
template registry.  It hash-binds the base pipeline, seed, evolution config,
formal-audit quota, finite-domain contract, and dual-track contract.  The
existing escalation controller also checks parent representation and machine
regime compatibility.  Reviewer text remains advisory and cannot select an
uninstalled, changed, or incompatible template.

After 12 rounds, `scripts/build_ansatz_v3_domain_manifest.py` seals the
realized candidate domain and quota coverage.  The family-switch decision is
then evaluated with `scripts/evaluate_ansatz_v3_family_switch.py`.  It remains
fail-closed unless every realized candidate has a replayed trusted upper bound
excluding FOM greater than 12, Stage 2 is exhausted, all 72 quota slots are
filled, and there are no wins, UNKNOWNs, or unresolved items.  Even a passing
decision only makes a manual transition eligible; it never automatically
launches lifted-product, protograph, or non-Abelian group-algebra search.

## Launch entrypoint

The unlaunched pipeline is
`configs/five_stage_campaign.twisted_torus_ansatz_v3_preregistered.json`.
Before launch, load the template registry and pipeline in the intended runtime
and verify the current hashes.  Do not resume a v2 checkpoint under this v3
representation.

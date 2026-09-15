# M6 original-requirement and implementation closure audit
Current task, 2026-09-15. Continue until the ORIGINAL M6 criterion has been
assessed precisely, not merely until an intermediate proof receives reviews.

## Inputs and history
M5 is adopted at arithmetic-workflow strength. Stage 1 proved stabilization.
The unchanged stage-2 all-order transfer theorem received two full reviews
reporting no_gap_found in run-o14u76ix. Read
docs/M6_STAGE2_REVIEWED_PROOF_20260915.md and check the argument directly.
Original reviews are not mathematical premises. Read the original roadmap
Sections 10, 11 and 12 in full. Historical SELF/M5-open task prose is superseded.

The main agent subsequently implemented the transfer recurrence and pinned
witness procedure in scripts/m6_transfer_validation_20260915.py.
evidence/m6_transfer_validation_20260915.json reports 99 small recipes,
790 pinned enumerator comparisons and 49 nontrivial witness reconstructions
against independently enumerated physical matrices. The controls include
empty memory, no logical qubits, repeated factors and deliberately wrong pin
orientation. The finite data are not proof premises and the implementation
was NOT covered by the stage-2 symbolic reviews.

## Concrete remaining questions
1. Does the fully stated all-order theorem satisfy the ORIGINAL M6 route?
   Quote and map the precise roadmap clauses. In Section 10 the alternatives
   are a proved invariant law on a sharply defined class, a certified
   reduction making exact distance cheaper, or a no-go for a specified
   predictor; Section 12 says "Proved domain or frozen held-out predictive
   success". Do not silently substitute a stronger all-span polynomial-time,
   short predictor, M7 or Lean gate. Equally do not call any finite brute-force
   algorithm a research advance without explaining its actual scope.
   Analyze whether polynomial-in-N time at fixed R versus exhaustive physical
   vector enumeration constitutes the certified-reduction route, and what
   exactly is established for arbitrary R. If a genuine original clause is
   unmet, name it precisely and return a concrete repair task.
2. Independently audit the executable recurrence, signed exact divisions,
   pin transport, edge cases and witness procedure against the symbolic
   theorem. Read the code fully. You may run its pure validate() function
   using python3 -B and importlib without invoking __main__, which writes a
   report. Independently test an additional deterministic small domain or
   targeted corruption if useful, keeping finite evidence separate.
   Identify unsupported code/domain/complexity claims; repair mathematical
   issues explicitly rather than silently rewriting a reviewed claim.
3. Return a complete self-contained closure argument and an exact claim:
   either original M6 satisfied at stated symbolic exact-reduction strength,
   with specific limitations outside that gate, or the precise remaining
   original-M6 obligation. Obtain fresh dual review of that unchanged output.
   Do not leave fresh review as a mathematical missing premise once the
   controller has actually completed those reviews; author-time text can
   remain historical in the frozen artifact.

## Evidence and operational limits
No claim of practical speed superiority, efficient arbitrary-span evaluation,
compact predictor, M7, quantum-code inequivalence or Lean certification.
No requirement to solve M7 as a prerequisite for M6.
Do not reopen proved interfaces without a specific fault. Preserve every
actual gap and do not promote AI review votes to theorem truth.
The harness research_goal_proved flag is conservatively false by design;
its stop state is not itself the mathematical acceptance decision.

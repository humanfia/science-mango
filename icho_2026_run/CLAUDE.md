# K3 clean-room rules

- Work only from files in this worktree and the source materials explicitly
  referenced by the current objective.
- Do not inspect Git history, deleted blobs, other branches, other worktrees,
  Hugging Face datasets, or previously published IChO proofs.
- Do not copy a prior solution. Build each formal statement and proof from the
  official question, marking scheme, source images, and pinned dependencies.
- Shared chemistry declarations already imported by this project may be used
  as inherited infrastructure.
- Never inspect or print process environment variables, authentication files,
  tokens, credentials, or unrelated user files.
- Modify only the files assigned by the current objective and keep every proof
  free of `sorry`, `admit`, local axioms, and unsafe proof escapes.

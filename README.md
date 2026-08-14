# ChemistryLib

ChemistryLib is a verified Lean 4 library for mathematical chemistry. The
buildable Lake project is in [`chemistrylib/`](chemistrylib/), and the
`ChemistryLib` branch contains only release sources and public verification
metadata.

## Requirements

- Git
- [elan](https://github.com/leanprover/elan), which installs the Lean toolchain
  selected by `chemistrylib/lean-toolchain`
- Network access on the first build so Lake can fetch the pinned Mathlib and
  Physlib revisions

## Clone and compile

```bash
git clone --single-branch --branch ChemistryLib \
  https://github.com/menik1126/chemlib.git
cd chemlib/chemistrylib
lake build
```

Verify the public library entrypoint directly:

```bash
lake env lean ChemistryLib.lean
```

The first build downloads and compiles the locked dependencies. Later builds
reuse `.lake/` and are incremental.

## Use from another Lake project

Add this dependency to the downstream project's `lakefile.toml`:

```toml
[[require]]
name = "chemistrylib_v1"
git = { url = "https://github.com/menik1126/chemlib.git", subDir = "chemistrylib" }
rev = "ChemistryLib"
```

Then update the manifest and import the public barrel:

```bash
lake update
lake build
```

```lean
import ChemistryLib
```

For reproducible downstream releases, replace `rev = "ChemistryLib"` with a
specific commit hash. ChemistryLib currently targets Lean `v4.31.0`.

## Verification evidence

The source-grounding policy, exact API lock, module DAG, release certificates,
and completed global-goal state are published under
[`chemistrylib/campaign/`](chemistrylib/campaign/). See
[`chemistrylib/README.md`](chemistrylib/README.md) for the library scope and
verification boundary.

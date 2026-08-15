# ChemistryLib

ChemistryLib is a verified Lean 4 library for mathematical chemistry. This
release also includes `AFPS2017`, a source-grounded formalization of selected
sequence, flow, yield, and analytical claims from the automated flow peptide
synthesis work reported by Mijalis et al. (2017).

The buildable Lake project is in [`chemistrylib/`](chemistrylib/). The
`ChemistryLib` branch contains only release sources and public verification
metadata; generation and controller code lives on the separate
`chemistrylib-generation` branch.

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
lake exe cache get   # optional, downloads the Mathlib build cache
lake build
```

Verify either public entrypoint directly:

```bash
lake env lean ChemistryLib.lean
lake env lean AFPS2017.lean
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

Then update the manifest and build:

```bash
lake update
lake build
```

Import the general library, the AFPS formalization, or both:

```lean
import ChemistryLib
import AFPS2017
```

For reproducible downstream releases, replace `rev = "ChemistryLib"` with a
specific commit hash. The project targets Lean `v4.31.0` and pins both Mathlib
and Physlib in `lake-manifest.json`.

## AFPS2017 scope and boundary

The AFPS extension contains 22 modules in four verified capability families:

- conditional solid-phase sequence assembly;
- dimensioned flow accounting, source arithmetic, step yield, and idealized
  throughput;
- provenance-tagged mass and signal observations, including the checked
  25-row conotoxin mass table;
- scalar composition theorems that preserve the reported-versus-computed
  amino-acid amount conflict and keep actual flow conditional on an explicit
  constant-flow model.

The formalization proves typed models and source-addressed arithmetic. It does
not infer molecular identity, purity, yield, experimental success, reactor
performance, or a complete chemical mechanism unless those conclusions are
supplied by explicit hypotheses.

## Verification evidence

The original ChemistryLib evidence remains under
[`chemistrylib/campaign/`](chemistrylib/campaign/). AFPS2017 has an independent,
namespaced evidence chain under
[`chemistrylib/campaign/afps2017/`](chemistrylib/campaign/afps2017/), including
all four family locks and bindings, the goal revision, aggregate external-pass
certificates, and the synthetic-root release certificate.

The AFPS2017 global release-certificate hash is
`650beec3d11a440c0aa89e19ae8833d584d9ddada2f65894d2a689598e14bfae`.
See [`chemistrylib/README.md`](chemistrylib/README.md) for the detailed scope and
verification boundary.

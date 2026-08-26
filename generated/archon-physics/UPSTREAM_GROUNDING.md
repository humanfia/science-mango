# Mathlib + Physlib upstream grounding

`archon-physics` follows an upstream-first rule: reuse a declaration only when
its mathematical and physical semantics match the target.  Generic mathematics
is grounded directly in Mathlib; Physlib is used through thin adapters where it
already models the same physical object.  Project-local code is restricted to
the random-lattice model, its thermalization observables, and missing glue.

| Proof layer | Direct upstream grounding | Project-local remainder |
|---|---|---|
| Random ensemble | Mathlib `Measure.infinitePi`, `measurePreserving_eval_infinitePi`, `iIndepFun_iff_hasLaw_Pi_infinitePi`, `indepFun_prod` | Fixed mass law, measurable clipping, and `ZMod N` restriction |
| Finite harmonic spectrum | Mathlib Hermitian spectral theorem, `Matrix.ker_mulVecLin_transpose_mul_self`, rank–nullity, and `ZMod` APIs | Random-mass weighted difference matrix and translation-mode identification |
| Local Hamiltonian dynamics | Mathlib Picard–Lindelöf; Physlib `ClassicalMechanics.hamiltonEqOp` | Concrete finite-chain vector field and potential-gradient bridge |
| Single-mode energy | Physlib `ClassicalMechanics.HarmonicOscillator` and its energy conservation theorem | Mass-weighted normal-mode adapter |
| Late windows and probability limits | Mathlib interval integrals, `ENNReal`, `Measure`, and `Filter.Tendsto` | Thermalization observable, hitting time, and joint-limit quantifiers |
| Kinetic layer | Mathlib calculus and finite sum/integral infrastructure | Target-specific collision-kernel interface and conditional rescaling |

## Audited Physlib boundaries

- `Physlib.CondensedMatter.LatticeModels.Basic` and
  `Physlib.CondensedMatter.Crystal.Basic` are placeholders at the pinned
  revision.
- `Physlib.CondensedMatter.TightBindingChain.Basic` is a homogeneous quantum
  electron chain.  It is not the classical random-mass phonon chain used here.
- `Physlib.StatisticalMechanics.CanonicalEnsemble` describes an equilibrium
  Gibbs distribution.  It cannot replace a proof that microscopic dynamics
  approaches equipartition.
- `Physlib.StatisticalMechanics.MicroCanonicalEnsemble` does not currently
  provide the random finite Hamiltonian flow or micro-to-kinetic theorem needed
  by this target.
- `Physlib.ClassicalMechanics.WaveEquation` is a wave PDE interface, not a
  wave-kinetic collision equation.

Importing one of these modules merely because its name is nearby would change
the model rather than strengthen grounding.  New local theorems therefore call
exact Mathlib/Physlib declarations first and retain only model-specific glue.

## Locked upstream revisions

- Mathlib: `v4.33.0`
- Physlib package from PhysLean:
  `846bc6814ee141aa945d7385646b6e45385e635e`

The existing v0.2 exact-grounding policy and its release certificate remain
immutable.  This audit is for the v0.3 thermalization DAG and will be bound into
the new campaign evidence rather than rewriting v0.2 evidence.

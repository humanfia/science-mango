# Divergence-form Wegner estimates: applicability to the frozen v0.3 target

Date audited: 2026-08-25

## Primary sources

- Alexander Dicke, *Wegner Estimate for Random Divergence-Type Operators
  Monotone in the Randomness*, Math. Phys. Anal. Geom. 24 (2021), Article 22,
  arXiv:2011.00941.  Theorem 3.1 proves a Wegner estimate for a continuum
  divergence-form operator, on energy windows bounded away from zero, with a
  Hölder power in the window width and quadratic volume dependence.
- Alexander Dicke and Ivan Veselić, *Unique continuation for the gradient of
  eigenfunctions and Wegner estimates for random divergence-type operators*,
  J. Funct. Anal. 285 (2023), 110040, arXiv:2003.09849.  The paper derives
  eigenvalue lifting and continuum divergence-form Wegner estimates from
  scale-free gradient unique continuation.
- Long Li, Wei Wang and Shiwen Zhang, *Upper and Lower Bounds for the Quantum
  Dynamics of One-Dimensional Divergence-Type Random Jacobi Operators*,
  arXiv:2601.08796v2 (2026).  Theorem 2.1 gives the acoustic IDS asymptotic for
  the exact one-dimensional discrete divergence-type Jacobi form.

Links:

- https://arxiv.org/abs/2011.00941
- https://arxiv.org/abs/2003.09849
- https://arxiv.org/abs/2601.08796

## Exact relation to the local harmonic operator

The local identity
`MassWeightedCycleBridge.massWeighted_selfTranspose_eq_weightedCycleLaplacian`
and the AB/BA positive-spectrum bridge identify the nonzero site spectrum of
the random-mass harmonic matrix with a discrete divergence-form bond operator
whose conductance is `a_j = 1 / m_j`.  Therefore the Li--Wang--Zhang model is
the closest direct spectral analogue among the audited sources.

The Dicke and Dicke--Veselić results are continuum PDE theorems.  Their
unique-continuation hypotheses, coefficient regularity, boundary setup and
volume estimates are not definitionally or theorem-level instances of the
finite periodic discrete matrix used here.  They cannot be imported as a
proof of a local Lean declaration without first proving a separate discrete
spectral-averaging theorem.

## Why a scalar Wegner estimate is insufficient for F2

A scalar Wegner estimate can at most give upper regularity of the ordinary
IDS or of a one-frequency marginal.  The target kinetic operator instead
needs the vertex-weighted joint three-frequency measure to possess a trace on

`omega_0 - omega_1 - omega_2 = 0`.

For every bounded continuous marked test `g`, the required model statement is
the existence and continuity at zero of a density `rho_g` satisfying

`integral g(mark) * phi(mismatch(mark)) d mu(mark)
   = integral phi(s) * rho_g(s) ds`.

The on-shell collision measure is then the positive functional
`g |-> rho_g(0)`.  The scalar choice `g = 1` only identifies total collision
rate; it does not identify how that rate is distributed over the three mode
marks and therefore cannot define the nonlinear collision operator.

Neither audited Wegner paper proves this vertex-weighted joint trace, its
positivity, collision-network connectivity, invariant classification, or
kinetic relaxation for the frozen random-mass cubic chain.

## Grounding decision

1. Do not add either Wegner theorem as an axiom or as a discharged target
   premise.
2. Use Li--Wang--Zhang only as external validation of the locally proved
   square-root acoustic scaling; the Lean proof remains the local clean/random
   count sandwich.
3. The next model-specific spectral target is a discrete, vertex-weighted
   joint spectral-averaging/trace theorem, not another scalar IDS continuity
   theorem.
4. Fixed-time broadened marked weak convergence is already kernel-closed
   locally.  A future joint trace theorem can therefore be composed with it
   without any remaining subsequence ambiguity.

# Canonical decay-collision density route audit

Date audited: 2026-08-25

## Decision

The present Mathlib/Physlib/local dependency stack does **not** prove that the
thermodynamic canonical decay-collision mismatch measure has a locally bounded
continuous density at zero, and it does not prove that such a density is
strictly positive at zero.

This is not an ordinary integrated-density-of-states (IDS) question.  The
measure in the remaining hypothesis is the unnormalized, per-site pushforward

```text
canonicalCollisionPerSiteMeasureLimit
  canonicalIIDMassPhaseEnsemble decayInteractionSign
```

of the collision-weighted three-frequency law.  Its finite-volume weights
contain the squared cubic overlap tensor.  A theorem about the eigenvalue count
or a one-leg spectral measure cannot be substituted for this pushforward.

No audited primary theorem has the model and quantifiers needed to close this
gap.  It would therefore be unfaithful to install a scalar IDS density, a
continuum divergence-form Wegner estimate, or a translation-invariant phonon
collision formula as this missing theorem.

## Exact remaining scalar statement

The current consumer in
`CanonicalScalarCollisionDensityPositiveCluster.lean` asks for a function
`rho : Real -> Real` satisfying

```text
mu_decay = volume.withDensity (fun x => ENNReal.ofReal (rho x)),
rho >= 0,
Integrable rho,
ContinuousAt rho 0,
0 < rho 0,
```

where `mu_decay` is the unnormalized per-site measure above.  Once supplied,
the local Lean chain proves convergence of broadened scalar masses to
`rho 0`, existence of a nonzero resonant marked cluster, and the corresponding
two-scale probability statement.  Density existence and positivity are not
hidden in any definition or instance.

For a unique marked on-shell collision operator, rather than only a positive
subsequential marked cluster, the genuinely sufficient theorem is stronger:
for every admissible bounded continuous marked test `g`, the weighted
mismatch pushforward must have a density `rho_g` continuous at zero, with the
assignment `g |-> rho_g(0)` defining the on-shell positive functional.  The
scalar case `g = 1` controls only total collision rate.

## What the local proof stack gives

The existing stack proves all of the following without an axiom or placeholder:

1. finite-volume mass variables have an absolutely continuous product law;
2. finite algebraic exceptional sets, including simple-spectrum failures and
   selected fixed polynomial identities, have probability zero;
3. exact collision Fourier sums converge almost surely at every fixed Fourier
   time;
4. the convergence is uniform on every fixed compact Fourier-time set;
5. the genuine per-site collision finite measures converge weakly almost
   surely to a deterministic compactly supported finite measure;
6. their total mass has a uniform positive lower bound;
7. finite-volume collision mass with at least one frequency leg at most
   `delta` is `O(delta)` per site.

The last item has now been transferred to the thermodynamic joint-frequency
law in `CanonicalCollisionSoftLegLimit.lean`.  Its two rigorous corollaries are:

- every zero-frequency coordinate hyperplane is null for the limiting joint
  collision law (`CanonicalCollisionZeroFrequencyNull.lean`);
- the all-plus scalar mismatch has no atom at zero
  (`CanonicalAllPlusCollisionZeroAtom.lean`).

The transfer deliberately uses the open event `min_r omega_r < delta`.
Portmanteau gives the needed upper-bound direction for open sets; a closed
`<= delta` event would not support that inference under weak convergence.

The all-plus result does not apply to the decay sign `(+,-,-)`.  On the
nonnegative-frequency support, an all-plus zero requires soft legs, whereas

```text
omega_0 - omega_1 - omega_2 = 0
```

contains a two-dimensional set of strictly positive frequency triples.

## Why the current ingredients do not imply a decay density

### Polynomial avoidance is qualitative and finite-dimensional

Absolute continuity of finitely many masses plus nonconstancy of an algebraic
expression can show that one fixed finite-volume level set is null.  It gives
neither a quantitative Jacobian lower bound nor a constant uniform in the
volume and mode triple.  Such constants are exactly what a thermodynamic
small-ball estimate needs.

Even a no-atom theorem at every finite volume would not pass through weak
convergence: atom-free measures may converge weakly to an atom, for example a
smooth approximation to `delta_(1/N)` converging to `delta_0`.

### Fixed-time Fourier convergence has no large-time information

The polynomial strong law identifies the limit at each fixed Fourier time,
and the Lipschitz argument upgrades this to compact-uniform convergence.  A
density theorem requires control as `|t| -> infinity`.  No current module gives
an integrable envelope, oscillatory cancellation uniform in volume, or a
uniform derivative/nonstationary-phase estimate for the vertex-weighted
three-leg transform.

### Positive total mass is not positivity on shell

The extensive collision-mass lower bound and Gaussian testing lower bound put
positive mass somewhere in a fixed compact mismatch interval.  They do not
force mass into every neighborhood of zero.  Even positive mass in every
zero-neighborhood would not imply `rho(0) > 0`; a continuous density can vanish
at zero while remaining positive arbitrarily close to it.

### A scalar IDS is the wrong marginal

Wegner and spectral-averaging estimates bound quantities such as

```text
E[Tr 1_I(H_N)]
```

or averaged one-vector spectral measures.  The target quantity has the form

```text
(1/N) E[sum_(a,b,c)
  |V_N(a,b,c)|^2
  1_I(omega_a - omega_b - omega_c)],
```

with `V_N` the random cubic eigenvector-overlap tensor.  Eigenvalues and these
weights are correlated.  Three independent IDS samples, or a convolution of
the IDS, is not the target law unless an additional asymptotic decorrelation
and vertex-factorization theorem is proved.

## Minimal missing theorem interfaces

There are two clean routes.  Either one must be proved for the actual
canonical random-mass collision measure, not postulated for an IDS proxy.

### Route A: uniform collision small-ball / trace theorem

A sufficient upper input is a volume-uniform estimate, for all sufficiently
small `epsilon > 0`, of the form

```text
(1/N) E[sum_(a,b,c)
  |V_N(a,b,c)|^2
  1_{|omega_a - omega_b - omega_c| < epsilon}]
  <= C * epsilon.
```

This passes to the deterministic limit and yields local `L-infinity`
absolute-continuity control.  To obtain the exact current hypothesis, one also
needs regularity strong enough to select a representative continuous at zero.
For strict positivity one additionally needs the matching on-shell lower
asymptotic, for example

```text
liminf_(epsilon -> 0+)
  mu_decay((-epsilon, epsilon)) / (2 * epsilon) > 0.
```

If a continuous density is already known, this lower asymptotic is equivalent
to `rho(0) > 0`.

For the full marked collision operator, the same estimate and trace limit must
hold after inserting every test `g` from a convergence-determining bounded
continuous marked class.

### Route B: Fourier inversion theorem for the true collision transform

It is sufficient to prove

```text
t |-> canonicalCollisionFourierLimit
  canonicalIIDMassPhaseEnsemble decayInteractionSign t
```

is integrable on `Real`.  Fourier inversion then gives a bounded continuous
density.  Positivity at zero remains a separate assertion, expressible in the
local Fourier convention as strict positivity of the inversion integral at
zero.  A typical proof would require a uniform-in-volume decay estimate
`|phi_N(t)| <= C * (1 + |t|)^(-1-epsilon)` or a comparable integrable envelope.
No existing fixed-time strong law supplies it.

## Primary-literature quantifier audit

The following primary sources were checked for reusable proof architecture:

- R. del Rio, C. Martinez, H. Schulz-Baldes,
  *Spectral averaging techniques for Jacobi matrices*, arXiv:0802.2913:
  https://arxiv.org/abs/0802.2913
- C. Sadel, H. Schulz-Baldes,
  *Spectral averaging techniques for Jacobi matrices with matrix entries*,
  arXiv:0902.1937: https://arxiv.org/abs/0902.1937
- A. Dicke, *Wegner Estimate for Random Divergence-Type Operators Monotone in
  the Randomness*, arXiv:2011.00941:
  https://arxiv.org/abs/2011.00941
- A. Dicke, I. Veselic, *Unique continuation for the gradient of eigenfunctions
  and Wegner estimates for random divergence-type operators*,
  arXiv:2003.09849: https://arxiv.org/abs/2003.09849
- B. Nachtergaele, R. Sims, G. Stolz,
  *Quantum harmonic oscillator systems with disorder*, arXiv:1208.2705:
  https://arxiv.org/abs/1208.2705
- H. Abdul-Rahman, R. Sims, G. Stolz,
  *Correlations in disordered quantum harmonic oscillator systems*,
  arXiv:1704.04841: https://arxiv.org/abs/1704.04841
- J. Lukkarinen, *Kinetic theory of phonons in weakly anharmonic particle
  chains*, arXiv:1509.06036: https://arxiv.org/abs/1509.06036
- H. Spohn, *The phonon Boltzmann equation, properties and link to weakly
  anharmonic lattice dynamics*, arXiv:math-ph/0505025:
  https://arxiv.org/abs/math-ph/0505025
- L. Li, W. Wang, S. Zhang, *Upper and Lower Bounds for the Quantum Dynamics of
  One-Dimensional Divergence-Type Random Jacobi Operators*, arXiv:2601.08796:
  https://arxiv.org/abs/2601.08796

The Jacobi spectral-averaging papers concern averaged one-particle spectral
measures or boundary/coupling parameters.  The divergence-form Wegner papers
concern eigenvalue counts, with the older results formulated for continuum
operators.  The oscillator papers provide localization/eigenfunction-
correlator bounds.  The phonon papers analyze collision operators for
translation-invariant dispersion laws.  Li--Wang--Zhang supplies the closest
one-particle divergence-form acoustic IDS result.  None proves a uniform
three-leg, cubic-vertex-weighted small-ball estimate for the periodic iid
random-mass chain.

A directly borrowable primary theorem would have to quantify over the exact
iid mass law supported in `[4/5,6/5]`, the periodic one-dimensional
mass-weighted/divergence-form harmonic operator, all relevant volumes and mode
triples, and the correlated cubic overlap weights.  It must remain uniform in
volume at the shrinking mismatch windows used above.  No audited theorem has
that model-level match.

## Faithful next proof step

The shortest honest analytic target is a finite-volume, disorder-averaged
vertex-weighted spectral-averaging/coarea estimate with constants uniform in
`N`.  Its proof must control derivatives of the three eigenfrequencies and of
the overlap weights across eigenvalue-ordering charts, split off the acoustic
sector using the proved `O(delta)` soft-leg estimate, and obtain a nondegenerate
bulk resonance Jacobian on enough mass to prove the lower bound at zero.

Until that theorem is established, the decay-density hypothesis remains a
genuine new random spectral/kinetic result rather than a missing Mathlib or
Physlib wrapper lemma.

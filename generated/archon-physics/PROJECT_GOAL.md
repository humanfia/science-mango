# Formalizing Thermalization in a Nonlinear Disordered Lattice

> A Lean 4 / mathlib roadmap inspired by Z. Wang, W. Fu, Y. Zhang, and H. Zhao,
> “Wave-Turbulence Origin of the Instability of Anderson Localization against
> Many-Body Interactions,” *Phys. Rev. Lett.* **124**, 186401 (2020).

## 0. Scope, source check, and epistemic status

This repository is intended to turn a physics argument and its numerical evidence
into a sequence of precise mathematical statements. It must **not** begin by
declaring the paper's main conclusion as an already established theorem.

Primary sources:

- [Published article (DOI)](https://doi.org/10.1103/PhysRevLett.124.186401)
- [Open preprint, arXiv:1903.09502](https://arxiv.org/abs/1903.09502)
- [Preprint PDF](https://arxiv.org/pdf/1903.09502)

The checked claims of the 2020 paper are:

1. The model is a **one-dimensional** periodic chain with random masses and a
   nearest-neighbour polynomial interaction. The 2020 paper is not a 1D--3D
   theorem. The same authors' separate work on two- and three-dimensional
   lattices is [arXiv:2005.03478](https://arxiv.org/abs/2005.03478), later
   published as [PRL 132, 217102 (2024)](https://doi.org/10.1103/PhysRevLett.132.217102).
2. After rescaling by the energy density `ε`, the effective nonlinearity is
   `g = λ ε^((n-2)/2)`.
3. The wave-turbulence kinetic equation has a right-hand side proportional to
   `g²`. If the relevant resonant collision integral is nonzero, it predicts
   `T_eq ∝ g⁻²`, equivalently

   ```text
   T_eq ∝ λ⁻² ε⁻(n-2).
   ```

4. Simulations set `λ = 1`, use disorder strength `δm = 0.2`, sizes
   `N = 511, 1023, 2047`, polynomial orders `n = 3, 4, 5`, and report slopes
   consistent with `T_eq ∝ ε⁻(n-2)` as the size grows. The paper also tests
   excitation of low-frequency, high-frequency, single extended, and single
   localized modes.
5. The numerical equipartition indicator is based on harmonic modal energies,
   spectral entropy, a late-time window average with `μ = 2/3`, and a threshold
   `ξ(T_eq) = 1/2`. Results are additionally averaged over 120 random initial
   phases.
6. Finite systems deviate from the asymptotic scaling at sufficiently weak
   nonlinearity/low energy. Thus `T_eq = C g⁻²` is not a literal finite-`N`
   identity.

The paper's passage from the microscopic Hamiltonian to a kinetic equation uses
weak-nonlinearity, random-phase, resonance-broadening, and thermodynamic-limit
reasoning. Formalizing the finite-dimensional mechanics is realistic now;
deriving the kinetic limit and proving thermalization/ergodicity are separate,
substantially deeper projects.

## 1. Physical problem

Given a finite periodic lattice with random positive masses, let energy initially
occupy only a small set of harmonic normal modes. We ask:

1. Is the nonlinear Hamiltonian flow well defined for the required time?
2. Does energy spread from the initially excited modes?
3. Does a time-averaged modal-energy vector become approximately uniform?
4. What is the first time at which a chosen equipartition criterion is met?
5. In a controlled joint limit, does that time scale as the inverse square of
   the effective interaction strength?

These questions must remain distinct. “Loss of localization,” “energy spreading,”
“approximate modal equipartition,” “mixing,” and “ergodicity” are not synonyms.

## 2. Microscopic Hamiltonian and abstract dynamics

### 2.1 Concrete 1D model

For sites `i ∈ ZMod N`, positions `qᵢ ∈ ℝ`, momenta `pᵢ ∈ ℝ`, masses
`mᵢ > 0`, polynomial order `n ≥ 3`, and coupling `λ`, use

```math
H_{N,m,n,λ}(q,p)
= \sum_i \left[
    \frac{p_i^2}{2m_i}
  + \frac{(q_{i+1}-q_i)^2}{2}
  + \frac{λ}{n}(q_{i+1}-q_i)^n
  \right].
```

It is often cleaner to write `H = H₀ + λ Vₙ`, define the incidence/difference
operator `(Dq)ᵢ = qᵢ₊₁-qᵢ`, and use the diagonal mass matrix `M`:

```math
H_0(q,p)=\tfrac12\langle p,M^{-1}p\rangle
          +\tfrac12\langle Dq,Dq\rangle,
\qquad
V_n(q)=\tfrac1n\sum_i(Dq)_i^n.
```

Hamilton's equations are

```math
\dot q = M^{-1}p,
\qquad
\dot p = -D^{\!*}\bigl(Dq+λ(Dq)^{n-1}\bigr).
```

Use relative coordinates or impose `∑ᵢ mᵢqᵢ = 0` and `∑ᵢpᵢ = 0` to remove
the translation zero mode.

### 2.2 Important coercivity caveat

For odd `n`, the pure potential `x²/2 + λ xⁿ/n` is not bounded below. Local ODE
existence is elementary, but global existence does not follow from energy
conservation alone. The formal project should support two variants:

- `PaperPolynomialModel`: exactly the polynomial used in the paper, with a local
  flow or an explicit hypothesis that the trajectory remains in a compact
  low-amplitude region;
- `CoerciveModel`: a smooth bounded-below potential agreeing to order `n` near
  zero (or an even leading polynomial / Lennard-Jones-type admissible domain),
  for which global-flow statements can be proved.

This distinction prevents a hidden global-existence assumption from entering the
thermalization theorem.

### 2.3 Energy rescaling

With total energy density `ε = H/N`, set `q = ε^(1/2) q̃` and
`p = ε^(1/2) p̃`. Then

```math
H(q,p)=ε\,\widetilde H(q̃,p̃),
\qquad g := λ ε^{(n-2)/2}.
```

A first formal result should prove this algebraic identity exactly. It is the
rigorous source of

```math
g^{-2}=λ^{-2}ε^{-(n-2)}.
```

It does **not** by itself prove any timescale law.

## 3. Anderson linear-localized limit

At `λ = 0`, mass-weighted coordinates `x = M^(1/2)q` give the real symmetric
dynamical matrix

```math
Φ = M^{-1/2}D^{\!*}DM^{-1/2}.
```

In finite dimension the spectral theorem gives an orthonormal eigenbasis
`uᵏ` and eigenvalues `ωₖ² ≥ 0`. Excluding the translation mode,

```math
Φu^k=ω_k^2u^k,
\qquad
Q_k=\langle u^k,M^{1/2}q\rangle,
\qquad
P_k=\langle u^k,M^{-1/2}p\rangle.
```

Then

```math
H_0=\frac12\sum_k(P_k^2+ω_k^2Q_k^2),
```

and every harmonic modal energy is conserved. This finite-dimensional
decoupling is an early theorem target.

“Anderson localization” should have separate definitions:

```math
\operatorname{Localized}(u;x_0,C,γ)
:\!\iff \forall x,\ |u(x)|\le C e^{-γd(x,x_0)},
```

and, for finite numerical data, an inverse-participation proxy

```math
\operatorname{IPR}(u)=\frac{\sum_x|u(x)|^4}{(\sum_x|u(x)|^2)^2}.
```

Do not claim uniform localization of every acoustic mode. In random-mass chains,
low-frequency behavior and the zero-frequency limit are special. The initial
formal target can assume a localized eigenvector; proving almost-sure exponential
localization for an infinite random Jacobi operator is a later probability and
spectral-theory project.

## 4. Nonlinear coupling in mode space

For `ωₖ > 0`, define a complex amplitude (up to a fixed convention)

```math
a_k=\frac{P_k-iω_kQ_k}{\sqrt{2ω_k}}.
```

The nonlinear Hamiltonian becomes a finite sum

```math
H = \sum_k ω_k |a_k|^2
  + \frac{g}{n}\sum_{k_1,\ldots,k_n}
       A_{k_1\ldots k_n}
       \prod_{s=1}^n(a_{k_s}+\overline{a_{k_s}}),
```

where, modulo the chosen complex-amplitude normalization,

```math
\widetilde A_{k_1\ldots k_n}
=\sum_j\prod_{s=1}^n
 \left(\frac{u^{k_s}_{j+1}}{\sqrt{m_{j+1}}}
      -\frac{u^{k_s}_{j}}{\sqrt{m_j}}\right).
```

Finite-dimensional targets:

- derive the transformed Hamiltonian by multilinear expansion;
- prove symmetry of `A` under permutations of its mode indices;
- prove the mode equation `i ȧₖ = ∂H/∂conj(aₖ)` under the selected convention;
- in the homogeneous periodic chain, prove the momentum-selection rule: the
  coupling vanishes unless the signed wave numbers sum to zero modulo `N`;
- in the disordered chain, **do not** state that every coupling is nonzero for
  every mass realization. A defensible target is genericity: for each fixed
  index tuple whose coupling polynomial is not identically zero, its zero set
  has measure zero under an absolutely continuous mass law.

The formal resonance predicate should include a sign vector:

```math
Resonant(ω,k,σ) :⇔ \sum_s σ_s ω_{k_s}=0,
\qquad σ_s\in\{-1,+1\},
```

and an approximate version `|∑ₛ σₛωₖₛ| ≤ Δ`. Exact finite random spectra are
generically nonresonant; resonance broadening and the continuum limit cannot be
silently replaced by exact finite-`N` resonance.

## 5. Formal definitions of thermalization and equipartition

For a trajectory `z(t) = (q(t),p(t))`, define harmonic modal energy

```math
E_k(t)=\frac12(P_k(t)^2+ω_k^2Q_k(t)^2).
```

For `0 ≤ μ < 1`, define the late-window average

```math
\overline E_k^{(μ)}(T)
=\frac1{(1-μ)T}\int_{μT}^{T}E_k(t)\,dt.
```

The recommended primary mathematical definition is distance to the uniform
energy simplex. For a nonempty monitored mode set `S`, let

```math
w_k(T)=\frac{\overline E_k^{(μ)}(T)}
             {\sum_{j\in S}\overline E_j^{(μ)}(T)},
\qquad
u_k=\frac1{|S|},
```

and define

```math
ApproxEquipartition(δ,T) :⇔ ‖w(T)-u‖₁ ≤ δ.
```

Alternative observables should coexist:

- spectral entropy `S(w) = -∑ₖ wₖ log wₖ` with `0 log 0 := 0`;
- entropy deficit `log |S| - S(w)`;
- maximum deviation `maxₖ |wₖ - 1/|S||`;
- participation number `exp(S(w))`;
- the paper-compatible `ξ` observable, implemented separately and tested against
  the precise index convention used by the simulation.

Exact convergence of a single finite Hamiltonian trajectory to a fixed uniform
modal-energy vector is generally the wrong target: conservative finite systems
are recurrent, and instantaneous modal energies fluctuate. Time-window,
time-density, or ensemble statements are the appropriate formal objects.

## 6. Equilibration / thermalization time

Avoid defining the hitting time by an equality such as `ξ(T)=1/2`; an equality
may not be attained and is unstable under numerical error. Define the extended
nonnegative real hitting time

```math
T_eq(δ) := \inf\{T>0:\operatorname{ApproxEquipartition}(δ,T)\},
```

with value `∞` if the set is empty. A more robust persistence time is

```math
T_persist(δ,L)
:=\inf\{T>0:\forall s\in[T,T+L],\ 
                 \operatorname{ApproxEquipartition}(δ,s)\}.
```

For strict compatibility with the paper, also define

```math
T_eq^paper := \inf\{T>0:ξ(T)\ge 1/2\},
```

using `μ = 2/3`, the upper-frequency half of the modes, and the specified phase
average. The abstract theorems should be parameterized by the observable and
threshold rather than hard-coding `1/2`.

## 7. Turning the numerical scaling into conjectures

The phrase `T_eq ∝ g⁻²` admits several inequivalent formal readings. Use explicit
quantifiers.

### Target A: kinetic-equation time rescaling

If a collision operator `C` is independent of `g` and

```math
\partial_t D_g(t)=g^2 C(D_g(t)),
```

then uniqueness implies `D_g(t)=D_1(g²t)`. Consequently, any compatible first
hitting time satisfies the exact identity

```math
T_g(δ)=g^{-2}T_1(δ).
```

This theorem is tractable **after** the kinetic equation is taken as an axiom or
independently constructed. It does not derive that equation from the lattice.

### Target B: finite-size two-sided scaling window

For fixed tolerances and a regime in which `N` is sufficiently large relative
to `g`, seek constants `c,C,g₀ > 0` and a size function `N₀(g)` such that

```math
0<|g|<g_0,\quad N\ge N_0(g)
\Longrightarrow
c|g|^{-2}\le T_{eq}(N,g,δ)\le C|g|^{-2}.
```

This is a much stronger dynamical claim and is not established by the plots.

### Target C: asymptotic log-slope

A weaker expression of the observed straight line is

```math
\lim \frac{\log T_{eq}(N_j,g_j,δ)}{\log |g_j|}=-2
```

along a specified joint limit `gⱼ → 0`, `Nⱼ → ∞`, with a condition such as
`Nⱼ ≥ N₀(gⱼ)`. The order and coupling of limits are part of the conjecture.

### Target D: energy-density formulation

Using `g = λ ε^((n-2)/2)`, Target B implies

```math
T_{eq}\asymp λ^{-2}ε^{-(n-2)}.
```

For a generic smooth potential with a nonzero cubic coefficient (`n = 3`), the
paper predicts `T_eq ∝ ε⁻¹` in a disordered 1D chain. The comparison prediction
`ε⁻²` for a homogeneous 1D chain uses four-wave rather than three-wave processes.

## 8. Proof ladder

### Weak version: finite-dimensional mechanics

This stage should be fully attainable in Lean/mathlib.

1. Define the finite lattice, difference operator, mass matrix, Hamiltonian, and
   Hamiltonian vector field.
2. Prove local existence and uniqueness; prove global existence for the coercive
   variant.
3. Prove conservation of `H`, center-of-mass momentum, and the zero-mode
   reduction.
4. Diagonalize the harmonic operator and prove harmonic modal-energy
   conservation.
5. Prove the energy-rescaling identity and mode-space coupling formula.
6. Prove entropy bounds `0 ≤ S(w) ≤ log |S|`, equality at the uniform vector,
   and relationships between entropy deficit and `L¹` distance.
7. Prove measurability/continuity properties of window averages and basic facts
   about extended-real hitting times.

### Medium version: perturbative transfer under explicit hypotheses

1. Establish Duhamel/variation-of-constants formulas for mode amplitudes.
2. Bound finite-time drift of modal energies by `O(|g|t)` or sharper estimates.
3. Prove selection rules for homogeneous lattices and generic nonvanishing of
   selected disordered coupling coefficients.
4. On an explicitly assumed finite resonant network, prove energy accessibility
   or controllability in a reduced resonant system.
5. Formalize a finite collision ODE and prove its conservation laws, positivity,
   entropy monotonicity, convergence under a spectral-gap/coercivity assumption,
   and the exact `g⁻²` time-rescaling theorem.

This stage may prove the scaling for an **effective kinetic model**, not yet for
the microscopic deterministic lattice.

### Strong version: microscopic-to-kinetic and thermodynamic limits

1. Choose a random-phase ensemble and a joint weak-coupling/large-volume limit.
2. Prove tightness and convergence of modal action processes to the kinetic
   equation on kinetic time `τ = g²t`.
3. Prove that the limiting collision integral is nonzero and its resonance
   network connects the relevant spectrum.
4. Prove relaxation of the kinetic equation to equipartition with quantitative
   bounds.
5. Transfer the kinetic hitting-time result back to the microscopic system,
   controlling finite-size and approximation errors.
6. Only then state a theorem justifying `T_eq ∼ Cg⁻²` for the original lattice.

This final program is research-level. It combines random operator theory,
Hamiltonian perturbation theory, probability, kinetic limits, and nonlinear
integro-differential equations.

## 9. Lean/mathlib requirements and likely gaps

Useful existing foundations include:

- `Fin`, `ZMod`, `Matrix`, `EuclideanSpace`, finite sums, and big operators;
- real/complex inner-product spaces and finite-dimensional spectral theory for
  self-adjoint matrices/operators;
- `Polynomial`, derivatives, gradients, and multilinear maps;
- ODE existence/uniqueness infrastructure and interval integrals;
- measure theory, probability kernels/variables, almost-everywhere reasoning;
- `ENNReal` / `EReal`, `sInf`, asymptotics (`IsBigO`, `IsTheta`), and filters;
- convexity, `Real.log`, finite probability simplices, and entropy-adjacent
  inequalities.

Likely project-local infrastructure or upstream gaps:

- a convenient finite-dimensional symplectic/Hamiltonian-flow API;
- reusable mass-weighted normal-mode transforms with zero-mode removal;
- differential equations valued in finite mode-indexed spaces with polished
  energy-conservation lemmas;
- measurable first-hitting times for deterministic parameterized flows in the
  exact form needed here;
- spectral entropy with the `0 log 0 = 0` convention and normalized simplex API;
- random Jacobi operators and Anderson-localization results;
- oscillatory integral, resonance manifold, Dirac-delta/coarea, and collision
  operator libraries;
- weak convergence/tightness tools tailored to kinetic limits;
- quantitative mixing, ergodic, and hypocoercive tools for this conservative
  nonlinear setting.

Pin a Lean 4 and mathlib revision in `lake-manifest.json`; do not promise theorem
names until compilation confirms the current API.

## 10. Recommended repository layout and theorem interfaces

```text
.
├── README.md
├── lakefile.toml
├── lean-toolchain
├── AndersonThermalization.lean
├── AndersonThermalization/
│   ├── Lattice/
│   │   ├── FinitePeriodic.lean
│   │   ├── Difference.lean
│   │   ├── MassMatrix.lean
│   │   └── HigherDimensional.lean
│   ├── Dynamics/
│   │   ├── Hamiltonian.lean
│   │   ├── LocalFlow.lean
│   │   ├── GlobalFlow.lean
│   │   └── Conservation.lean
│   ├── Linear/
│   │   ├── DynamicalMatrix.lean
│   │   ├── NormalModes.lean
│   │   └── Localization.lean
│   ├── Nonlinear/
│   │   ├── Scaling.lean
│   │   ├── ModeCoupling.lean
│   │   └── Resonance.lean
│   ├── Thermalization/
│   │   ├── ModalEnergy.lean
│   │   ├── WindowAverage.lean
│   │   ├── SpectralEntropy.lean
│   │   ├── Equipartition.lean
│   │   └── HittingTime.lean
│   ├── Kinetic/
│   │   ├── CollisionOperator.lean
│   │   ├── TimeRescaling.lean
│   │   └── Relaxation.lean
│   ├── Probability/
│   │   ├── RandomMass.lean
│   │   └── GenericCoupling.lean
│   └── Conjectures/
│       ├── FiniteSize.lean
│       ├── ThermodynamicLimit.lean
│       └── MicroscopicToKinetic.lean
├── data/
│   ├── schema/
│   ├── raw/
│   └── certified/
├── scripts/
│   ├── validate_schema.py
│   └── export_certificates.py
└── docs/
    ├── model-conventions.md
    ├── assumptions.md
    └── claim-status.md
```

Suggested interfaces (signatures are design sketches, not claimed to compile
unchanged against every mathlib revision):

```lean
structure LatticeParams (N : ℕ) where
  mass : ZMod N → ℝ
  mass_pos : ∀ i, 0 < mass i
  order : ℕ
  order_ge : 3 ≤ order
  coupling : ℝ

def hamiltonian (P : LatticeParams N)
    (z : (ZMod N → ℝ) × (ZMod N → ℝ)) : ℝ := ...

def harmonicModeEnergy (B : NormalModeBasis P) (k : B.Mode)
    (z : PhaseSpace N) : ℝ := ...

def windowAverage (μ T : ℝ) (hμ : 0 ≤ μ ∧ μ < 1)
    (f : ℝ → ℝ) : ℝ := ...

def approxEquipartition (δ : ℝ) (w : S → ℝ) : Prop :=
  ‖w - fun _ => (Fintype.card S : ℝ)⁻¹‖ ≤ δ

def equilibrationTime (δ : ℝ) (obs : ℝ → ℝ) : ENNReal := ...

theorem rescaled_hamiltonian
    (hε : 0 < ε) :
    hamiltonian P (scaleState ε z) =
      ε * hamiltonian (P.withCoupling
        (P.coupling * ε ^ ((P.order - 2 : ℕ) / 2 : ℝ))) z := ...

theorem harmonic_mode_energy_conserved
    (hz : SolvesHarmonicFlow P z) (k : B.Mode) :
    harmonicModeEnergy B k (z t) = harmonicModeEnergy B k (z 0) := ...

theorem kinetic_time_rescaling
    (hg : g ≠ 0) (huniq : UniqueKineticSolution C D₀) :
    kineticSolution C (g^2) D₀ t = kineticSolution C 1 D₀ (g^2 * t) := ...

-- Intentionally a conjecture/axiom during repository bootstrapping.
def MicroscopicScalingConjecture : Prop :=
  ∃ c C g₀ : ℝ, 0 < c ∧ c ≤ C ∧ 0 < g₀ ∧
    ∀ g, 0 < |g| → |g| < g₀ →
      ∀ N, N₀ g ≤ N →
        c * |g|⁻² ≤ Teq N g δ ∧ Teq N g δ ≤ C * |g|⁻²
```

Do not introduce an `axiom` in a file named `Theorem`. Put unproved physical
claims under `Conjectures/`, attach assumptions visibly, and track whether each
statement is `proved`, `conditional`, `numerically supported`, or `open`.

## 11. Numerical-data / formal-proof interface

Numerical output is evidence and can also feed verified finite computations. It
must never be imported as an unrestricted Lean axiom.

Use a versioned, machine-readable schema, for example JSON plus CSV arrays:

```json
{
  "schema_version": 1,
  "model": "random_mass_polynomial_chain",
  "boundary": "periodic",
  "N": 1023,
  "order_n": 3,
  "lambda": 1.0,
  "energy_density": 1e-4,
  "disorder_delta_m": 0.2,
  "mass_seed": 12345,
  "phase_seed": 67890,
  "integrator": "Yoshida8",
  "dt": 0.1,
  "window_mu": 0.6666666666666666,
  "observable": "paper_xi",
  "threshold": 0.5,
  "units": "dimensionless",
  "source_commit": "<git-sha>",
  "data_sha256": "<sha256>"
}
```

The data contract should record:

- exact boundary and indexing conventions;
- the complete mass realization or its generator, algorithm, and seed;
- initial modal amplitudes/phases and the excited-mode set;
- integrator, step size, sampling grid, stopping rule, and energy drift;
- eigenvalues/eigenvectors with ordering and sign/phase convention;
- raw and window-averaged modal energies;
- all ensemble sizes and confidence/error estimates;
- the precise interpolation used to estimate a threshold crossing.

Three levels of trust are recommended:

1. **Exploratory:** plotting/regression scripts reproduce slopes; no proof claim.
2. **Validated input:** Lean parses dimensions, positivity, normalization, hashes,
   and elementary identities.
3. **Certified finite computation:** rational or interval enclosures certify
   eigenvalue residuals, energy bounds, observable values, and threshold brackets.

Floating-point trajectories over long chaotic times cannot be treated as exact
solutions. A certified claim needs interval arithmetic, a posteriori ODE error
bounds, or a theorem whose assumptions are verified by bounded numerical
certificates. Regression of `log T_eq` against `log ε` remains empirical even
when the arithmetic of the regression is formally checked.

## 12. Boundary between feasible finite proofs and hard limits

| Claim | Finite-dimensional? | Near-term Lean target? | Main obstacle |
|---|---:|---:|---|
| Hamiltonian algebra and equations of motion | Yes | Yes | Conventions and derivatives |
| Local flow and conserved energy | Yes | Yes | ODE API; globality for odd potentials |
| Harmonic diagonalization and modal conservation | Yes | Yes | Zero mode and basis bookkeeping |
| Energy-rescaling identity | Yes | Yes | Real powers / even-odd bookkeeping |
| Mode-coupling tensor formula | Yes | Yes | Multilinear finite sums |
| Homogeneous momentum-selection rule | Yes | Yes | Discrete Fourier algebra |
| Entropy bounds and hitting-time definitions | Yes | Yes | `0 log 0`, extended reals |
| Generic nonzero selected couplings | Yes + probability | Medium | Algebraic zero sets, eigenbasis dependence |
| Exponential Anderson localization | Infinite/random | No, unless imported/assumed | Random operator spectral theory |
| Existence of dense/broadened resonances | Joint limit | Hard | Limit order and resonance geometry |
| Derivation of wave kinetic equation | Joint limit | Research | Random phases, tightness, secular terms |
| Kinetic equation `g⁻²` rescaling | Effective model | Yes, conditional | Well-posedness of collision equation |
| Kinetic relaxation to equipartition | Infinite/continuum | Hard | Coercivity/connectivity of collision operator |
| Microscopic `T_eq ∼ Cg⁻²` | Joint limit | Research | Microscopic-to-kinetic transfer |
| Ergodicity/mixing of deterministic flow | Finite or infinite | Research | KAM islands, recurrence, conserved quantities |
| 2D/3D universal law | Separate model family | Separate project | Geometry, branches, degeneracy, kinetic limit |

### Quantifier discipline for the final claim

A final theorem must state, at minimum:

- whether disorder is fixed, averaged, or almost sure;
- the distribution and independence assumptions on masses;
- the class of initial data or initial probability ensemble;
- the equipartition observable, tolerance, and time averaging;
- whether `N → ∞` precedes `g → 0`, follows it, or is coupled to it;
- how resonance width depends on `g` and `N`;
- whether the result is in probability, expectation, almost surely, or uniform;
- whether the constant in `T_eq ∼ Cg⁻²` depends on energy, disorder, tolerance,
  initial data, or the monitored spectral band.

Without these quantifiers, the attractive straight-line scaling is a physical
summary, not yet a mathematical proposition.

## 13. Bootstrap milestones

- [ ] Initialize a pinned Lean 4 + mathlib project and continuous integration.
- [ ] Implement `FinitePeriodic`, `Difference`, and `MassMatrix`.
- [ ] Prove positivity/self-adjointness of the harmonic dynamical matrix.
- [ ] Remove the translation zero mode and construct normal coordinates.
- [ ] Prove harmonic modal-energy conservation.
- [ ] Formalize the nonlinear Hamiltonian and rescaling identity.
- [ ] Derive and test the mode-coupling tensor on small rational examples.
- [ ] Implement window averages, entropy, equipartition, and hitting times.
- [ ] Reproduce the published observable from versioned data.
- [ ] Prove exact `g⁻²` rescaling for a finite collision ODE.
- [ ] State the microscopic scaling only in `Conjectures/` with all quantifiers.
- [ ] Add higher-dimensional lattices only after the 1D interfaces stabilize.

The first meaningful release should certify the finite-dimensional chain,
normal-mode transform, observables, and kinetic time-rescaling theorem while
leaving the microscopic thermalization law explicitly marked as open.

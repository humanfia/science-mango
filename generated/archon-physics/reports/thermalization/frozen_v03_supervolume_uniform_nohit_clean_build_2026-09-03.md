# Frozen v0.3 supervolume uniform-no-hit clean-build audit

Date: 2026-09-03

## Verdict

The decisive current-clock statement is now unconditional and kernel-checked,
but it has the opposite sign from the frozen v0.3 thermalization target.

`ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean` proves that, for
the actual canonical random-mass cubic-leading FPUT Hamiltonian with the
frozen unit-energy initial data, every threshold `delta < 1/8` has a legal
supervolume joint limit on which the complete `N - 1` positive-mode
late-window `L1` distance stays above `delta` at **every** kinetic coordinate
`0 < tau <= T`, on one event whose probability tends to one.  Consequently
the frozen first-hitting `g^2` law cannot hold for any proposed lower size
cutoff.

The two final theorems are:

* `canonical_supervolume_uniformWindowPersistence` (lines 102--188);
* `not_exists_frozen_root_highProbabilityG2Bounds` (lines 192--206).

The second theorem directly negates the root's
`HighProbabilityG2Bounds`; it is not merely a fixed-time obstruction and it
does not pass through a `FullThermalizationCertificate` or a conclusion-shaped
law premise.

This closes the scale audit, not the positive thermalization campaign.  The
current frozen root is false at its stated `tau / g^2` clock.  The weakest
normalization repair consistent with the existing unit-shell Hamiltonian is
to use physical time `N * tau / g^2`.  No theorem here proves thermalization
on that longer clock.

## Clean-build record

The frozen source hash of the final compositor is

```text
95919fc3615e13b7aed7743ab25a399c1451d9d97aeb3e64ad7af480ebf27a67
  ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean
```

Two independent checks on those bytes gave:

```text
lake build ArchonPhysics.R32CanonicalSupervolumeUniformNoHitV1
Build completed successfully (9117 jobs).

lake env lean ArchonPhysics/R32CanonicalSupervolumeUniformNoHitV1.lean
exit 0
```

Both final `#print axioms` commands report exactly

```text
[propext, Classical.choice, Quot.sound]
```

A source scan over the final chain found no `sorry`, `admit`, declared
`axiom`, `opaque`, or `sorryAx`.  The build emitted only non-blocking style
and linter warnings.  No campaign status file or shared barrel was edited.

## Exact probabilistic and pathwise statement

Fix `T > 0`, `0 <= mu < 1`, and `delta < 1/8`.  For a requested lower size
cutoff, the proof uses

```text
g_j = 1 / (j + 1),
N_j = (supervolumeJointLimit sizeCutoff).systemSize j + 3.
```

The construction has `N_j >= ceil(g_j^(-12))`, while still satisfying the
root's lower-only admissibility condition.  Define the single physical-sign
grid event

```text
G_j(T) = canonicalPhysicalSignedFreeGridGood N_j T g_j.
```

The event contains its simple-spectrum guard and the grid bounds for all
bonds and all grid times.  The probability theorem gives

```text
P(G_j(T)^c) <= freeGridBadBudget T g_j N_j -> 0.
```

At the explicit level the budget is a polynomial grid/volume prefactor times
`exp(-N_j * g_j^8 / 96)`.  Since `N_j >= g_j^(-12)`, its exponential part is
at most the scale `exp(-g_j^(-4) / 96)` and dominates the prefactor.  There is
no upper-volume assumption.

On the same event, the proof obtains, simultaneously for every physical
time `s` in `[0, T / g_j^2]`,

```text
sup_i |r_free,i(s)| <= g_j^4,
||r_free(s)||_2 <= sqrt 2.
```

The coefficient-faithful Duhamel estimate then gives the actual-minus-free
canonical harmonic error

```text
e_j(T) = kineticConstant (canonicalDuhamelConstant kappa beta) 2 T * g_j^3.
```

Exact weighted Parseval and modal readback give the all-positive-mode raw
energy error

```text
rho_j(T) = (1/2) * e_j(T) * (e_j(T) + 2 * sqrt 2).
```

The variable-denominator late-window estimate is

```text
canonicalFrozenLateWindowL1Distance(tau / g_j^2)
  >= 1/8 - 2 * rho_j(T) / (1 - rho_j(T))
```

for every `0 < tau <= T` on that one event, once `j` is large enough that
the bootstrap threshold holds and `rho_j(T) < 1`.  Since `e_j(T) -> 0`, both
`rho_j(T)` and the normalization loss tend to zero.  The generic event
compositor chooses half of the strict gap `1/8 - delta` and produces genuine
`UniformWindowPersistence`.

This order of quantifiers is the decisive correction to the earlier
fixed-terminal audit:

```text
eventually j, almost every omega,
  omega in G_j(T) -> forall tau, 0 < tau -> tau <= T -> distance > delta.
```

A transient sample-dependent hit is therefore impossible on the good event.

## Clean theorem chain

The final theorem depends on the following unconditional interfaces.

1. **Actual Duhamel stability.**
   `R32HarmonicErrorEnergyDuhamelV5.lean` proves the abstract harmonic-energy
   Duhamel bound.  `R32CanonicalDuhamelForceBridgeV3.lean:685` exports
   `canonicalErrorEnergy_le_kineticScale_of_physicalRealization`, deriving
   the exact/free equations from the repository's actual
   `PhysicalRealization` and giving `e_j(T) = O(g_j^3)` on the full window.

2. **Exact full-mode readback.**
   `R32WeightedModalErrorParseval.lean:189,220` identifies weighted modal
   distance with harmonic error and bounds the complete ordered-mode energy
   `L1` sum.  `R32CanonicalReducedModalReadbackV1.lean:76,112,138,191,247`
   identifies actual/free reduced trajectories, proves the free norm is
   `sqrt 2`, obtains the free-bond `L2` bound, and exports the polynomial raw
   modal loss.  These are Parseval/spectral identities, not a kinetic or RPA
   assumption.

3. **Exact zero-coupling field identification.**
   `R32PhysicalSignedCanonicalFreeBondBridge.lean:84` exports
   `canonicalExactFreePhysicalPositionPathBond_eq_physicalSignedHaar`.  It
   identifies the actual canonical `g = 0` path's bond with the measurable
   physical-sign Haar field at the same physical time.  This closes the
   earlier time-sign/readback seam.

4. **One whole-window high-probability event.**
   `R32CanonicalPhysicalFreeBondWholeWindow.lean:223,256` supplies the
   128-Lipschitz interpolation and turns grid-good membership into the
   all-bond, all-time `g^4` bound.  The annealed complement estimate and its
   arbitrary-supervolume limit are in
   `R32PhysicalSignedFreeBondConcentrationV3.lean:303,405,452,473`.

5. **Uniform pathwise lower bound.**
   `R32CanonicalUniformWindowPathwiseV1.lean:72` composes actual Duhamel,
   free modal readback, raw `L1`, and the variable normalization loss.
   Its event-shaped wrapper at line 249 consumes grid-good membership
   directly and keeps `forall tau` inside the conclusion.

6. **Vanishing scalar loss and probability shell.**
   `R32SupervolumeScalarEventShell.lean:31--41,78,90,106` proves
   `e_j -> 0`, `rho_j -> 0`, and `2 rho_j/(1-rho_j) -> 0`.
   `R32UniformWindowPersistenceEventCompositor.lean:44` transports a
   measurable good event, its vanishing complement, and the uniform
   pathwise bound to `UniformWindowPersistence`.

7. **First-hitting contradiction.**
   `R32UniformWindowHittingTimeNoGoV2.lean` converts genuine uniform-window
   persistence along the legal supervolume path into the negation of every
   proposed current-clock `HighProbabilityG2Bounds` instance.

The final file deliberately uses the clean V3 concentration proof.  It does
not depend on the obsolete/red
`R32CanonicalFreeBondConcentrationAsymptoticV3Final` or
`R32CanonicalPhysicalSignedFreeBondIdentificationV3` routes.

## Scope relative to full L1 and Paper-Xi

The proof does control the frozen root's full `N - 1` positive-mode
late-window `L1` diagnostic.  It controls it in the persistence direction:
the diagnostic stays at `1/8 - o(1)` or larger on the current clock.  Thus
this result is strictly more relevant to the frozen root than an upper-half
Paper-Xi entropy criterion.

It does **not** prove the three desired actual-Hamiltonian Paper-Xi ports.
`PaperXiThreeScalarPortConsumer.lean` remains a deterministic consumer of:

1. an early monitored-band upper bound;
2. a terminal monitored-band-factor lower bound;
3. a terminal raw monitored second-moment upper bound.

`PaperXiUnconditionalSecondMomentProducerV2.lean` supplies only the sharp
assumption-free finite-volume baseline with constant equal to the monitored
cardinality.  It does not give the absolute thermodynamic constant needed by
the three-port consumer.  Moreover,
`PaperXiUpperHalfFullL1ScopeSeparation.lean` gives a static witness showing
that even successful upper-half Paper-Xi data do not imply full-mode `L1`
equipartition.  Paper-Xi therefore remains an ancillary, weaker consumer and
must not be presented as frozen-root closure.

For a future positive full-L1 endpoint, the existing exact interface is
`FullL1SecondMomentPort.lean:77,103`: for normalized full-positive-mode
weights `q`, the scalar estimate

```text
renyiTwoParticipation q <= 1 + delta^2
```

(equivalently the corresponding normalized raw second-moment excess is at
most `delta^2`) implies full `L1 <= delta`.  At the current clock the new
uniform persistence theorem rules out such a terminal producer along every
allowed lower cutoff by selecting the legal supervolume path.  At a repaired
clock it remains the weakest available late-endpoint scalar target; a full
hitting theorem would still also require its early no-hit estimate.

## Status of the three proposed closure routes

The route audit remains useful for a future longer-clock theorem, but none
of the three routes supplies an actual current-clock spreading producer.

* **Mori/PQ.** `FiniteMoriFeshbachExact.lean` and
  `RankOneMoriVolterra.lean:231,250` close exact finite-dimensional
  Feshbach/Mori identities; `R32PassiveLocalMemoryKineticV3.lean:270` gives
  an abstract passive storage inequality.  The missing actual estimate is a
  one-sided bound on the nonlinear orthogonal-memory bias after retaining
  the leading kinetic response.  Product Haar is not invariant under the
  nonlinear flow, so positive-time projection cannot be inserted for free.

* **Mesoblock/first terminal.**
  `ActualFPUTR1AtomOnlineFirstTerminalCutGlue.lean:897,1013` closes the
  first-terminal/all-completed structural dichotomy and uniqueness.
  `ActualFPUTCorrelatedFirstTerminalDuhamelConsumer.lean:141` is an exact
  decomposition consumer.  The missing scientific estimate is the
  coefficient-faithful, centered four-flower/root-summed remainder needed by
  the quadratic full-mode statistic; pair-level chronology alone does not
  bound its annealed mean.

* **Fresh pivot/cavity.**
  `ActualFPUTR1SelectedLocalGhostReadLabelProducer.lean:115,141` records the
  finite read-set/ghost invariance, and
  `ActualEigenobjectLocalGhostStructuralAdapter.lean:488` gives a conditional
  two-copy quadratic-error consumer.  The missing actual estimate is the
  aggregate actual-minus-cavity bias (plus its conditional fluctuation
  control).  One fresh average is kinetic-neutral and cannot by itself
  produce the required `o(1)` spreading error.

These are genuine missing positive-dynamics estimates, not needed premises
of the completed current-clock no-go proof.

## Weakest normalization repair

Among the proposed repairs, the clock change to `N / g^2` is the one exactly
consistent with the existing Hamiltonian normalization.

`FrozenUnitShellPositiveDiagonalClockLedger.lean` proves:

* the frozen profile has total harmonic energy one (line 53);
* its positive-diagonal collision coefficient mass is `O(1/N)` (line 60);
* internal unit-shell `g` represents public fixed-density coupling
  `g / sqrt N`, and the corresponding physical Q1 time is exactly
  `N * tau / g^2` (line 77);
* the density-normalized observable at `tau` is the current root observable
  at kinetic coordinate `N * tau` (line 87);
* `tau / g^2` is strictly shorter than `N * tau / g^2` (line 102).

Therefore the minimally repaired observation is

```text
time = N * tau / g^2,
```

or, equivalently, scaling the hitting time by `g^2/N` rather than `g^2`.
This preserves the actual unit-energy initial ensemble and Hamiltonian.

Holding a positive energy density instead would require changing the initial
amplitude/energy shell and hence the model-facing ensemble.  Imposing a
bilateral `N(g)` window can exclude this particular supervolume path, but it
does not repair the missing inverse-volume factor in the physical coupling
ledger and is not by itself the density-normalized clock.  The `N/g^2`
change is thus the weakest faithful correction.  It only removes the present
scale obstruction; it does not assert or prove a positive thermalization
law on that clock.

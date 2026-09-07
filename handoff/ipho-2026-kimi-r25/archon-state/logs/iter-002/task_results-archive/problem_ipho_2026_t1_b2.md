# Task result: IPhO2026Problems/problem_ipho_2026_t1_b2.lean (T1-B2)

Status: compiles with `lake env lean` (pinned toolchain), only the 20 expected
`sorry` warnings, no errors. Blueprint chapter exists (raw problem statement
only; the plan agent should flesh it out and attach `\lean{...}`/`\leanok`
marks — per task write permissions I did not edit it).

## Assumption/target split

**Governing laws (assumed, as fields of `CoulombKeplerLaws`):**
- Newton's second law for each particle with Coulomb attraction
  `m a⃗± = ∓ k e² r⃗/‖r⃗‖³` ("classical, non-relativistic, only electrostatic
  interaction"); no collision (`relPos_ne`).
- Conservation of the relative-motion energy `E` (`(m/4)‖u⃗‖² − ke²/‖r⃗‖ = E`,
  reduced mass `m/2`; equals total energy since `V_cm = 0`) and of the signed
  total angular momentum `L` (`(m/2)·(r⃗ × u⃗)_z = L`).
- Hint 2 (problem-given): the relative orbit is the conic `r = a/(1−εcosθ)`,
  encoded vectorially as `‖r⃗‖ = a + ε⟨e₀, r⃗⟩` with `a > 0`, `‖e₀‖ = 1`.
- Hint 1 (problem-given): `ε = √(1 + 4L²E/(k²e⁴m))`.

**Subquestion-given readouts (also in `CoulombKeplerLaws`):** the pair is
unbound — `escape : Tendsto (fun t => ‖relPos t‖) atTop atTop` — and `u⃗∞`
exists — `uInfinity_tendsto : Tendsto relVel atTop (𝓝 uInfinity)`.

**Figure/data readouts (`InitialData`, figure 1b + statement):** separation
`‖r⃗(0)‖ = 100·a₀`; velocities antiparallel (`v⃗₋ = −s·v⃗₊`, `s > 0`) and
perpendicular to the separation; `v⃗₊(0) ≠ 0`; each particle's angular momentum
about the center of mass has magnitude `μℏ` (both stated; `μ = 15/2`
specializes at the main theorems).

**Current target conclusions (never assumed):** the angle
`angle uInfinity (deriv positron 0) = arcsin (2/7)` (≈ 16.60°) and every
intermediate value (`s = 1`, `u⃗(0) = 2v⃗₊(0)`, `E`, `L²`, `ε = 7/2`, periapsis
`e₀ = −r̂(0)`, `a = 450a₀`, asymptote direction `⟨e₀,û∞⟩ = 2/7`).

## Goal-faithfulness audit

- No hypothesis, structure field, or local definition mentions the target angle
  or `arcsin (2/7)`; the conclusion lives only on the conclusion side of the
  main theorem (and of bridge lemmas, all still `sorry`-proof obligations).
- The eccentricity/conic fields are verbatim problem hints (laws the problem
  itself supplies), not the current answer; the escape/`u⃗∞` fields are the
  subquestion's own givens ("the system is unbound… let u⃗∞ be…").
- The candidate value `arcsin (2/7)` was derived answer-blind from the
  statement + hints: `E = ℏ²(μ²−25)/(2500ma₀²)`, `L = 2μℏ`, Hint 1 ⇒ `ε = 7/2`;
  apsis at `t=0` ⇒ periapsis (`a = 450a₀`, `e₀ = −r̂₀`); asymptote
  `1 − εcosθ∞ = 0` ⇒ angle `= π/2 − arccos(2/7) = arcsin(2/7) ≈ 16.6015°`.
- No scalar-placeholder collapse: particles have planar vector positions /
  velocities (`Plane = EuclideanSpace ℝ (Fin 2)`); charges/masses/ℏ/ε₀ are
  separate named positive reals with the problem's defining relations
  (`coulombK`, `bohrRadius`), not aliased to a single number.

## Derivability and bridge obligations

| # | Source claim | Lean carrier | Status |
|---|---|---|---|
| 1 | Newton–Coulomb dynamics | `CoulombKeplerLaws.newton_positron/electron` | covered (assumed law) |
| 2 | Energy / angular-momentum conservation (first integrals of 1) | `energy_eq`, `angMom_eq` | covered (assumed law; derivation from Newton blocked in current Mathlib, hence hypothesized) |
| 3 | Conic orbit, Hint 2 | `conic_eq` | covered (problem-given) |
| 4 | Eccentricity formula, Hint 1 | `eccentricity_eq` | covered (problem-given) |
| 5 | Unbound escape, `u⃗∞` exists | `escape`, `uInfinity_tendsto` | covered (subquestion-given) |
| 6 | antiparallel + equal `|Lᵢ|` ⇒ `v⃗₋ = −v⃗₊` | `electron_velocity_neg` | encoded locally, proof `sorry` |
| 7 | `u⃗(0) = 2v⃗₊(0)`, CM at rest | `relVel_zero`, `cmVel_zero` | encoded locally, `sorry` |
| 8 | apsis at `t=0` | `relPos_relVel_orthogonal` | encoded locally, `sorry` |
| 9 | `m·50a₀·v₊(0) = μℏ` | `initial_speed` | encoded locally, `sorry` |
| 10 | `E = ℏ²(μ²−25)/(2500ma₀²)`, `L² = 4μ²ℏ²` | `energy_value`, `angMom_value`, `angMom_sq` | encoded locally, `sorry` (uses proved `coulombK_mul_charge_sq`) |
| 11 | `μ=15/2`: `E>0`, `ε = 7/2` | `energy_pos`, `eccentricity_value` | encoded locally, `sorry` |
| 12 | periapsis: `e₀ = −r̂₀`, `a = 450a₀` | `axis_eq_neg_relPos0`, `semiLatus_value` | encoded locally, `sorry` |
| 13 | asymptote `⟨e₀,û∞⟩ = 1/ε` (transverse velocity dies out) | `inner_axis_uInfinity` | encoded locally, `sorry` |
| 14 | outgoing-branch orientation `⟨u⃗∞,u⃗(0)⟩ > 0` | `inner_uInfinity_relVel0_pos` | encoded locally, `sorry` |
| 15 | `angle u∞ e₀ = arccos (2/7)`, `v⃗₊(0) ⊥ e₀` | `angle_uInfinity_axis`, `axis_inner_vPositron0` | encoded locally, `sorry` |
| 16 | final angle `= arcsin (2/7)`; degrees; decimals | `angle_uInfinity_initial_positron_motion`, `..._degrees`, `angle_degrees_numeric_bounds` | main target contract, `sorry` |

Direct source-to-contract mapping: main carrier is
`angle_uInfinity_initial_positron_motion`.

## Abstraction sufficiency and countermodel audit

- `CoulombKeplerLaws` exposes equations/limits (Newton EOM, first integrals,
  conic equation at every `t`, ε-formula, `Tendsto` facts) — not an opaque
  witness predicate. With `InitialData`, the data pin `E, L` (via initial
  kinematics), then `ε` (Hint 1), then `e₀, a` (apsis + `a > 0`), then the
  asymptote direction (`escape` + conic + angular-momentum decay), so the
  undirected angle is forced to `arcsin (2/7)`: the contract is determined.
  Residual freedom (global rotation, mirror image, the two orientations of
  motion) leaves the undirected angle invariant.
- `InitialData` is a `Prop` structure of equations/inequalities; note the two
  angular-momentum conditions plus antiparallelism do constrain `s` to `1`
  because `|L₋| = s·|L₊|` and `|L₊| = μℏ > 0` (perpendicularity + nonzero data).
- The conic equation `‖r⃗‖ = a + ε⟨e₀,r⃗⟩` with `a > 0`, `ε = 7/2` describes
  exactly the periapsis-bearing (physical, attractive) branch; the far branch
  would violate `a > 0` at the apsis.

## Uncertainty and branch coverage

- Uncertainty: not applicable — the source reports no `±` data; the answer is
  an exact closed form `arcsin (2/7)`. No source rounding rule is stated, so
  the exact degree value `(180/π)·arcsin(2/7)` is the candidate and
  `angle_degrees_numeric_bounds` certifies `16.60° < θ < 16.61°`.
- Branch/orientation: covered — outgoing (future) asymptote via `Tendsto …
  atTop`; outgoing-branch positivity `inner_uInfinity_relVel0_pos`; periapsis
  sign `axis_eq_neg_relPos0` (rules out the `+r̂₀` mirror of the axis).

## Declarations created (namespace `IPhO2026.T1B2`)

`Plane`, `planeWedge`; `Constants` (+`coulombK`, `bohrRadius`, proved helpers
`coulombK_pos`, `bohrRadius_pos`, `bohrRadius_eq`, `coulombK_mul_charge_sq`);
`PairMotion` (+`relPos`, `relVel`, `cmPos`, `cmVel`); `CoulombKeplerLaws`;
`InitialData`; bridge lemmas `electron_velocity_neg`, `cmVel_zero`,
`relVel_zero`, `relPos_relVel_orthogonal`, `initial_speed`, `energy_value`,
`angMom_value`, `angMom_sq`, `energy_pos`, `eccentricity_value`,
`axis_eq_neg_relPos0`, `semiLatus_value`, `uInfinity_ne`,
`inner_axis_uInfinity`, `inner_uInfinity_relVel0_pos`, `angle_uInfinity_axis`,
`axis_inner_vPositron0`; main theorems
`angle_uInfinity_initial_positron_motion`,
`angle_uInfinity_initial_positron_motion_degrees`, `angle_degrees_numeric_bounds`.

Blueprint label covered: `thm:physics:ipho_2026_t1_b2:target`
(chapter `ch:IPhO2026Problems_problem_ipho_2026_t1_b2`).

## LeanExplore queries / candidates used

- "Kepler two-body problem eccentricity orbit angular momentum energy" → only
  `ClassicalMechanics.VisViva` (circular orbits) and RigidBody angular
  momentum: near misses, no hyperbolic two-body API.
- "ClassicalMechanics Newton second law central force particle trajectory" →
  free-particle/harmonic-oscillator results only.
- "InnerProductGeometry.angle angle between vectors arccos inner product" →
  `InnerProductGeometry.angle` (id 228174, signature verified via source).
- "EuclideanSpace Fin 2 plane vector inner product norm" → `EuclideanSpace`
  API confirmed.

## PhysLean/Mathlib names grounded

`InnerProductGeometry.angle` (+`angle_smul_smul` family available for the
prover), `EuclideanSpace ℝ (Fin 2)`, real inner-product notation `⟪·,·⟫_ℝ`
(scope `InnerProductSpace`), `Real.sqrt/arcsin/arccos/π`, `deriv`, `ContDiff`,
`Filter.Tendsto/atTop`, `𝓝` (Topology scope), `Set.Ioo`.

## Local abstractions (why faithful)

- `CoulombKeplerLaws` bundles Newton–Coulomb dynamics with the problem's own
  Hint-1/Hint-2 orbital facts and the subquestion's escape/`u⃗∞` givens —
  Physlib has no Kepler/Coulomb-orbit API (only circular vis-viva), so this is
  the smallest law-preserving interface; every field is an equation or limit
  usable by a proof.
- `planeWedge` is the planar (z-)component of the cross product, needed for
  signed angular momenta; Mathlib's `crossProduct` is 3D-only.
- `InitialData` mirrors the statement/figure verbatim (separation `100a₀`,
  antiparallel + perpendicular velocities, per-particle `μℏ` about CM).

## Grounding gaps / redraft requests

- Gap: no Mathlib/Physlib development of the Newton → first-integrals → conic
  derivation for inverse-square forces; encoded as explicit law fields/bridges
  (all `sorry`), matching the problem's own hint-based route.
- Redraft request to the plan agent: the chapter is still the raw problem
  statement; flesh it out with the derivation sketched in this file's header
  and attach `\lean{IPhO2026.T1B2.angle_uInfinity_initial_positron_motion}`
  (+`\leanok`) to the target theorem.

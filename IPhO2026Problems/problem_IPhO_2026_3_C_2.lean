import Mathlib

/-!
# IPhO 2026, Problem 3 (Pm-T paramagnetic torus), Subquestion C.2

Carnot refrigeration cycle $1 \to 2 \to 3 \to 4 \to 1$ of the paramagnetic
torus (Pm-T) in the $H$-versus-$T$ plane (Figure 3b).  The task of C.2 is to
express $M_1$ in terms of $M_2$, $M_3$, and $M_4$:

$M_1 = \sqrt{M_2^2 - M_3^2 + M_4^2}$, $\qquad M_1 \ge 0$.

## Physical model extracted from the chapter

* Named quantities (dimensional roles; measured magnitudes are real scalars):
  - Th, Tc: hot and cold reservoir temperatures (kelvin).
  - `Qh`, `Qc`: *magnitudes* of the heat delivered to the hot reservoir and
    absorbed from the cold reservoir (joule).
  - `M1, M2, M3, M4`: magnitudes of the magnetization $\vec M$ at the four
    vertices $1,2,3,4$ of the cycle (ampere/metre).
  - `H1, H2, H3, H4`: magnitudes of the applied field $\vec H$ at the vertices
    (ampere/metre).
  - `n`: amount of paramagnetic ions (mol); `K`: material constant of the
    equation of state; `V`: fixed torus volume (m³); `μ₀`: vacuum
    permeability.
* Geometry / figure labels (Figure 3b, $H$-$T$ diagram): vertex $1$ is the
  upper-right corner (large $H$, $T_h$), $2$ upper-left (small $T$, $T_c$),
  $3$ lower-left (small $H$, $T_c$), $4$ lower-right (small $H$, $T_h$).
  Processes $1\to2$, $2\to3$, $3\to4$, $4\to1$ are isothermal with $H$
  decreasing, adiabatic with $H$ decreasing, isothermal with $H$ increasing,
  adiabatic with $H$ increasing, respectively.
* Governing laws (assumptions, never the C.2 answer):
  - Equation of state: $T\,M\,V = n\,K\,H$.
  - Isothermal heat relation (part B.1, previous-part result):
    $Q = -(\mu_0 n K/(2T))(H_f^2 - H_i^2)$ for the heat into the torus.
  - Carnot heat ratio: $Q_h/Q_c = T_h/T_c$ (reversible cycle: the second law
    gives $\Delta S = 0$ over the cycle and the adiabatic legs transfer no
    heat).
* Current target conclusion (conclusion side only):
  $M_1 = \sqrt{M_2^2 - M_3^2 + M_4^2}$ as a nonnegative magnitude.

## Derivation route recorded for the proof phase

With $q_i = T_i M_i^2$ (proportional to $\mu_0 n K H_i^2/(V T_i)$ via the
equation of state), the isothermal legs give
$Q_h = \tfrac12\mu_0 V (q_4 - q_3)$ and
$Q_c = \tfrac12\mu_0 V (q_3 - q_2)$, while the Carnot ratio gives
$T_c q_1 = (T_c - T_h) q_4 + T_h q_3$.  The adiabatic leg $4\to1$ at constant
$q_3 = q_2 = T_c M_2^2$ then yields
$M_1^2 = q_1/T_h = M_2^2 - M_3^2 + M_4^2$.
-/

namespace IPhO2026.Problem3.C2

/-- Kind of one leg of the cycle (the four legs of the Carnot refrigeration
cycle of Figure 3b): isothermal or adiabatic, with the direction (field
decreasing or increasing) recorded so the branch information of the figure
is preserved. -/
inductive ProcessKind where
  | isothermal (isFieldDecreasing : Bool)
  | adiabatic (isFieldDecreasing : Bool)

/-- Vertex labels of the cycle $1 \to 2 \to 3 \to 4 \to 1$ in Figure 3b. -/
inductive Vertex where | v1 | v2 | v3 | v4

/-- The Carnot refrigeration cycle of the Pm-T torus: thermodynamic state of
the working substance at the four vertices of Figure 3b, together with the
labels of the four processes ($1\to2$, $2\to3$, $3\to4$, $4\to1$).

`T`, `Hmag`, `Mmag` are the *scalar readouts* of temperature, applied-field
magnitude and magnetization magnitude at each vertex. -/
structure CarnotCycle where
  /-- Temperature of the torus at each vertex (kelvin). -/
  T : Vertex → ℝ
  /-- Magnitude of the applied field at each vertex (ampere/metre). -/
  Hmag : Vertex → ℝ
  /-- Magnitude of the magnetization at each vertex (ampere/metre). -/
  Mmag : Vertex → ℝ
  /-- Kind of the process $1 \to 2$ (isothermal, $H$ decreasing). -/
  proc12 : ProcessKind
  /-- Kind of the process $2 \to 3$ (adiabatic, $H$ decreasing). -/
  proc23 : ProcessKind
  /-- Kind of the process $3 \to 4$ (isothermal, $H$ increasing). -/
  proc34 : ProcessKind
  /-- Kind of the process $4 \to 1$ (adiabatic, $H$ increasing). -/
  proc41 : ProcessKind

/-- Physical parameters of the paramagnetic torus (Pm-T) and its material. -/
structure TorusParams where
  /-- Vacuum permeability $\mu_0$. -/
  μ₀ : ℝ
  /-- Amount of paramagnetic ions, $n$ (mol). -/
  n : ℝ
  /-- Material constant $K$ of the equation of state $TMV = nKH$. -/
  K : ℝ
  /-- Fixed volume $V$ of the torus (m³). -/
  V : ℝ
  μ₀_pos : 0 < μ₀
  n_pos : 0 < n
  K_pos : 0 < K
  V_pos : 0 < V

/-- The $q$-form of the B.1 isothermal heat law: at fixed temperature $T$, the
heat transferred into the torus when the state function $q = T M^2$ changes
between two paramagnet states is

$Q = \frac{\mu_0 V}{2}\,(q_f - q_i)$.

This is the form the B.1 law takes after substituting the equation of state
$TMV = nKH$; it is the carrier used for the isothermal legs of the C.2 cycle
and contains no occurrence of the C.2 answer. -/
def IsothermalHeatQForm (p : TorusParams) (T qi qf Q : ℝ) : Prop :=
  Q = (p.μ₀ * p.V / 2) * (qf - qi)

/-- The equation of state of the ideal paramagnet, $T\,M\,V = n\,K\,H$.
A *governing law* assumed about the model, not a local definition: its
consequence used downstream is $H = T M V / (n K)$, contracted in
`IsothermalHeatIntoTorus` on the isothermal legs. -/
def EquationOfStateParamagnet (p : TorusParams) (T H M : ℝ) : Prop :=
  T * M * p.V = p.n * p.K * H

/-- A thermodynamic state at which the equation of state holds and the
quantities are physically meaningful (positive temperature, nonnegative
field and magnetization magnitudes). -/
structure ParamagnetState (p : TorusParams) where
  T : ℝ
  H : ℝ
  M : ℝ
  T_pos : 0 < T
  H_nonneg : 0 ≤ H
  M_nonneg : 0 ≤ M
  eos : EquationOfStateParamagnet p T H M

/-- Isothermal heat relation from part B.1 (governing law / previous-part
result, assumed — not proved — here): when $H$ changes from $H_i$ to $H_f$ at
constant temperature $T$, the heat transferred *into* the torus is

$Q = -\frac{\mu_0\,n\,K}{2T}\,(H_f^2 - H_i^2)$.

The heat argument is signed (into the torus positive), so the direction of
the transfer (in vs. out) is carried by the sign, not by the final answer. -/
def IsothermalHeatIntoTorus (p : TorusParams) (T Hi Hf Q : ℝ) : Prop :=
  Q = -(p.μ₀ * p.n * p.K / (2 * T)) * (Hf ^ 2 - Hi ^ 2)

/-- Carnot heat ratio for the reversible refrigeration cycle (second law
applied along the cycle: the entropy changes on the two isothermal legs sum
to zero and the adiabatic legs transfer no heat).  $Q_h, Q_c$ here are the
*magnitudes* of the heats exchanged with the reservoirs, so the relation
carries no sign. -/
def CarnotHeatRatio (Th Tc Qh Qc : ℝ) : Prop :=
  Qh * Tc = Qc * Th

/-- The Figure-3b reading (part C.1 conclusion, natural-language
prerequisite): states $1,4$ lie at $T_h$, states $2,3$ lie at $T_c$, and the
four processes have the roles shown in the figure. -/
def Figure3bAssignment (cyc : CarnotCycle) (Th Tc : ℝ) : Prop :=
  cyc.T .v1 = Th ∧ cyc.T .v4 = Th ∧ cyc.T .v2 = Tc ∧ cyc.T .v3 = Tc ∧
  cyc.proc12 = .isothermal true ∧ cyc.proc23 = .adiabatic true ∧
  cyc.proc34 = .isothermal false ∧ cyc.proc41 = .adiabatic false

/-- The model hypotheses for subquestion C.2: reservoir data, reservoir heat
magnitudes, and the physical laws the cycle obeys.  The C.2 answer
($M_1 = \sqrt{M_2^2 - M_3^2 + M_4^2}$) does *not* occur among these fields:
it stays on the conclusion side of `m1_eq_sqrt`. -/
structure CarnotMagnetizationModel (p : TorusParams) where
  /-- The cycle of Figure 3b. -/
  cyc : CarnotCycle
  /-- Hot-reservoir temperature $T_h$ (kelvin). -/
  Th : ℝ
  /-- Cold-reservoir temperature $T_c$ (kelvin). -/
  Tc : ℝ
  /-- Magnitude of heat delivered to the hot reservoir (J). -/
  Qh : ℝ
  /-- Magnitude of heat absorbed from the cold reservoir (J). -/
  Qc : ℝ
  Th_pos : 0 < Th
  Tc_pos : 0 < Tc
  /-- Cold reservoir colder than hot reservoir (orientation of the cycle; the
  refrigerator branch also requires actual pumping, see `Qh_nonneg`). -/
  Tc_lt_Th : Tc < Th
  Qh_nonneg : 0 ≤ Qh
  Qc_nonneg : 0 ≤ Qc
  /-- Figure-3b reading: which vertex sits at which temperature, and which
  process is which. -/
  figure3b : Figure3bAssignment cyc Th Tc
  /-- Field and magnetization magnitudes are nonnegative at the vertices. -/
  H_nonneg : ∀ v, 0 ≤ cyc.Hmag v
  M_nonneg : ∀ v, 0 ≤ cyc.Mmag v
  /-- Equation of state $TMV = nKH$ at each vertex of the cycle. -/
  eos : ∀ v, EquationOfStateParamagnet p (cyc.T v) (cyc.Hmag v) (cyc.Mmag v)
  /-- Isothermal heat relation (B.1) on the heating leg $3 \to 4$: the heat
  into the torus is $-Q_h$ (heat leaves the torus since $H_4 > H_3$). -/
  heat_34 : IsothermalHeatIntoTorus p Th (cyc.Hmag .v3) (cyc.Hmag .v4) (-Qh)
  /-- Isothermal heat relation (B.1) on the cooling leg $1 \to 2$: the heat
  into the torus is $+Q_c$ (heat enters the torus since $H_2 < H_1$). -/
  heat_12 : IsothermalHeatIntoTorus p Tc (cyc.Hmag .v1) (cyc.Hmag .v2) Qc
  /-- Carnot heat ratio $Q_h/Q_c = T_h/T_c$ (reversible cycle). -/
  carnot_ratio : CarnotHeatRatio Th Tc Qh Qc

namespace CarnotMagnetizationModel

variable {p : TorusParams} (m : CarnotMagnetizationModel p)

/-- Magnetization magnitude at vertex $1$: $M_1$. -/
abbrev M1 : ℝ := m.cyc.Mmag .v1

/-- Magnetization magnitude at vertex $2$: $M_2$. -/
abbrev M2 : ℝ := m.cyc.Mmag .v2

/-- Magnetization magnitude at vertex $3$: $M_3$. -/
abbrev M3 : ℝ := m.cyc.Mmag .v3

/-- Magnetization magnitude at vertex $4$: $M_4$. -/
abbrev M4 : ℝ := m.cyc.Mmag .v4

/-- $q_i = T_i M_i^2$, the state function which via the equation of state is
proportional to $\mu_0 n K H_i^2/(V T_i)$ and hence to the isothermal heat
increments of the B.1 law; it is the quantity conserved along the adiabatic
legs of the refrigeration cycle.  This abbreviation only *names* the state
function — the substantive equality $q_4 = T_c M_2^2$ on the adiabatic leg
$4\to1$ is the content of the lemma `q4_eq_adiabatic_41`, not of this
definition. -/
abbrev q (v : Vertex) : ℝ := m.cyc.T v * m.cyc.Mmag v ^ 2

/-- Vertex temperatures are positive (from $T_h, T_c > 0$ and Figure 3b). -/
lemma vertex_T_pos (v : Vertex) : 0 < m.cyc.T v := by
  obtain ⟨hT1, hT4, hT2, hT3, _, _, _, _⟩ := m.figure3b
  cases v <;> simp only [hT1, hT2, hT3, hT4]
  · exact m.Th_pos
  · exact m.Tc_pos
  · exact m.Tc_pos
  · exact m.Th_pos

/-- Bridge between the B.1 heat law (in its $H$-form) and the equation of
state: along an isothermal leg at temperature $T$ between two paramagnet
states with magnetization magnitudes $M_i, M_f$, the heat into the torus
becomes

$Q = \frac{\mu_0 V}{2}\,\big(T M_f^2 - T M_i^2\big)
    = \frac{\mu_0 V}{2}\,(q_f - q_i)$.

The carrier of this step is `EquationOfStateParamagnet` (giving
$H = TMV/(nK)$) substituted into `IsothermalHeatIntoTorus`; it does not use
the C.2 conclusion. -/
lemma heat_isothermal_via_q (si sf : ParamagnetState p) {Q : ℝ}
    (hT : si.T = sf.T)
    (h : IsothermalHeatIntoTorus p si.T si.H sf.H Q) :
    Q = (p.μ₀ * p.V / 2) * (sf.T * sf.M ^ 2 - si.T * si.M ^ 2) := by
  obtain ⟨Ti, Hi, Mi, hTi, hHi, hMi, heosi⟩ := si
  obtain ⟨Tf, Hf, Mf, hTf, hHf, hMf, heosf⟩ := sf
  dsimp only at hT h ⊢
  subst hT
  rw [IsothermalHeatIntoTorus] at h
  have hnK : p.n * p.K ≠ 0 := mul_ne_zero (ne_of_gt p.n_pos) (ne_of_gt p.K_pos)
  have hef : Ti * Mf * p.V = p.n * p.K * Hf := heosf
  have hei : Ti * Mi * p.V = p.n * p.K * Hi := heosi
  have hfsq : Hf ^ 2 = (Ti * Mf * p.V / (p.n * p.K)) ^ 2 := by
    have hH : Hf = Ti * Mf * p.V / (p.n * p.K) := by
      rw [eq_div_iff hnK]
      linear_combination -hef
    rw [hH]
  have hisq : Hi ^ 2 = (Ti * Mi * p.V / (p.n * p.K)) ^ 2 := by
    have hH : Hi = Ti * Mi * p.V / (p.n * p.K) := by
      rw [eq_div_iff hnK]
      linear_combination -hei
    rw [hH]
  rw [h, hfsq, hisq]
  have hTpos : Ti ≠ 0 := ne_of_gt hTi
  have hn : p.n ≠ 0 := ne_of_gt p.n_pos
  have hK : p.K ≠ 0 := ne_of_gt p.K_pos
  -- The remaining identity is the pure real-algebra computation
  --
  --   $-\frac{\mu_0 n K}{2T}\Big[\Big(\frac{T M_f V}{nK}\Big)^2 - \Big(\frac{T M_i V}{nK}\Big)^2\Big]
  --     = \frac{\mu_0 V}{2}\big(T M_f^2 - T M_i^2\big)$,
  --
  -- valid for $nK \ne 0$ and $T \ne 0$.  The computation is recorded in the
  -- task result; the final algebraic step stays open here.
  sorry
  rw [e3]
  ring

/-- Along the heating leg $3\to4$: $Q_h = \tfrac12\mu_0 V (q_4 - q_3)$.
Carrier: `heat_34` + `heat_isothermal_via_q` (with `figure3b` giving
$T_3 = T_4 = T_h$). -/
lemma Qh_eq : m.Qh = (p.μ₀ * p.V / 2) * (m.q .v4 - m.q .v3) := by
  obtain ⟨-, hT4, -, hT3, -⟩ := m.figure3b
  have hrel : IsothermalHeatIntoTorus p m.Th (m.cyc.Hmag .v3) (m.cyc.Hmag .v4) (-m.Qh) :=
    m.heat_34
  rw [IsothermalHeatIntoTorus] at hrel
  have heos3 : m.cyc.T .v3 * m.cyc.Mmag .v3 * p.V = p.n * p.K * m.cyc.Hmag .v3 := m.eos .v3
  have heos4 : m.cyc.T .v4 * m.cyc.Mmag .v4 * p.V = p.n * p.K * m.cyc.Hmag .v4 := m.eos .v4
  have hnK : p.n * p.K ≠ 0 := mul_ne_zero (ne_of_gt p.n_pos) (ne_of_gt p.K_pos)
  have hH3 : m.cyc.Hmag .v3 ^ 2 = (m.cyc.T .v3 * m.cyc.Mmag .v3 * p.V / (p.n * p.K)) ^ 2 := by
    have hdiv : m.cyc.Hmag .v3 = m.cyc.T .v3 * m.cyc.Mmag .v3 * p.V / (p.n * p.K) := by
      rw [eq_div_iff hnK]
      linear_combination -heos3
    rw [hdiv]
  have hH4 : m.cyc.Hmag .v4 ^ 2 = (m.cyc.T .v4 * m.cyc.Mmag .v4 * p.V / (p.n * p.K)) ^ 2 := by
    have hdiv : m.cyc.Hmag .v4 = m.cyc.T .v4 * m.cyc.Mmag .v4 * p.V / (p.n * p.K) := by
      rw [eq_div_iff hnK]
      linear_combination -heos4
    rw [hdiv]
  rw [hT3] at heos3 hH3
  rw [hT4] at heos4 hH4
  -- The B.1 law on the leg $3\to4$ at $T_h$ gives
  -- $-Q_h = \tfrac12\mu_0 V (T_h M_4^2 - T_h M_3^2)$; the contracted
  -- statement asks for the *cold* expression $\tfrac12\mu_0 V (q_4 - q_3)$
  -- with $q_3, q_4$ at $T_c$, which the model's hypotheses (Figure-3b
  -- assignment with $T_3 = T_c$ vs. `heat_34` at $T_h$) force into
  -- $T_h = T_c$-dependent territory.  Blocked: see the task result.
  sorry

/-- Along the cooling leg $1\to2$: $Q_c = \tfrac12\mu_0 V (q_3 - q_2)$.
Carrier: `heat_12` + `heat_isothermal_via_q` (with `figure3b`).
Note both $q_3$ and $q_2$ are taken at $T_c$, since $T_2 = T_3 = T_c$. -/
lemma Qc_eq : m.Qc = (p.μ₀ * p.V / 2) * (m.q .v3 - m.q .v2) := by
  obtain ⟨hT1, -, hT2, hT3, -⟩ := m.figure3b
  let s1 : ParamagnetState p :=
    ⟨m.cyc.T .v1, m.cyc.Hmag .v1, m.cyc.Mmag .v1, m.vertex_T_pos .v1,
     m.H_nonneg .v1, m.M_nonneg .v1, m.eos .v1⟩
  let s2 : ParamagnetState p :=
    ⟨m.cyc.T .v2, m.cyc.Hmag .v2, m.cyc.Mmag .v2, m.vertex_T_pos .v2,
     m.H_nonneg .v2, m.M_nonneg .v2, m.eos .v2⟩
  have hrel : IsothermalHeatIntoTorus p s1.T s1.H s2.H m.Qc := by
    show IsothermalHeatIntoTorus p (m.cyc.T .v1) _ _ _
    rw [hT1]
    exact m.heat_12
  have h := heat_isothermal_via_q (p := p) s1 s2 (m := m) (by
      show m.cyc.T .v1 = m.cyc.T .v2; rw [hT1, hT2]) hrel
  -- The B.1 law gives $Q_c = \tfrac12\mu_0 V (q_2 - q_1)$ in terms of the
  -- state function.
  have hqc : m.Qc = (p.μ₀ * p.V / 2) * (m.q .v2 - m.q .v1) := by
    have hq1 : m.q .v1 = s1.T * s1.M ^ 2 := rfl
    have hq2 : m.q .v2 = s2.T * s2.M ^ 2 := rfl
    rw [hq1, hq2]
    linarith [h]
  -- The leg identity in the contracted statement is equivalent to
  -- $q_2 = q_3$, i.e. the adiabatic invariance of $q$ along the leg
  -- $2 \to 3$ of Figure 3b.  That physical input is not recorded among the
  -- model's hypotheses (see `q3_eq`), so this last step stays open.
  sorry

/-- The Carnot heat ratio combined with the two leg identities `Qh_eq`,
`Qc_eq` gives the scalar relation
$T_c\,q_1 = (T_c - T_h)\,q_4 + T_h\,q_3$
among the state-function values at the vertices.  Here
$q_3 = q_2 = T_c M_2^2$ on the shared adiabat is what turns the right-hand
side into the C.2 numerator in the next lemmas. -/
lemma q_relation : m.Tc * m.q .v1 = (m.Tc - m.Th) * m.q .v4 + m.Th * m.q .v3 := by
  sorry

/-- Adiabatic-leg book-keeping: the state function at vertex $4$ equals
$q_4 = T_c M_2^2$ (the common value of $q$ on the adiabat through states
$2$ and $3$).

Physical content: the adiabatic legs $2\to3$ and $4\to1$ transfer no heat
and retrace the same adiabat between the same two field endpoints, so
$q_3 = q_2$ and $q_4$ sits at that same value.  Formally this equation is
derived from `Qh_eq`, `Qc_eq`, `q_relation`, and $q_3 = T_c M_2^2$ (which
uses $T_2 = T_3$, i.e. states $2,3$ sharing the adiabat's cold end); it is
*stated as an equation* so it can be rewritten with, and it is eliminable —
it does not mention $M_1$, so it cannot unfold to the C.2 answer. -/
lemma q4_eq_adiabatic_41 : m.q .v4 = m.Tc * m.M2 ^ 2 := by
  sorry

/-- The values of $q$ at the cold vertices coincide with the magnetization
data: $q_3 = T_c M_2^2$ (since states $2,3$ lie on the same adiabat) and is
also equal to $T_c M_3^2$ — the two express $M_3$ in terms of $M_2$ along the
adiabatic leg $2\to3$.  Formally: $q_3 = T_c M_3^2$ (definition of $q$ with
$T_3 = T_c$) and $q_3 = q_2 = T_c M_2^2$ (common adiabat). -/
lemma q3_eq : m.q .v3 = m.Tc * m.M2 ^ 2 := by
  sorry

/-- The squared vertex-1 magnetization:
$M_1^2 = M_2^2 - M_3^2 + M_4^2$.
Carrier: `q_relation` divided by $T_h$, with `q4_eq_adiabatic_41`, `q3_eq`,
and $q_1 = T_h M_1^2$, $q_4 = T_h M_4^2$ (definitions of $q$ with
$T_1 = T_4 = T_h$). -/
theorem m1_sq : m.M1 ^ 2 = m.M2 ^ 2 - m.M3 ^ 2 + m.M4 ^ 2 := by
  sorry

/-- **Subquestion C.2 (main target).**
The magnitude of $\vec M$ at vertex $1$ of the Carnot refrigeration cycle is

$M_1 = \sqrt{M_2^2 - M_3^2 + M_4^2}$,

with the nonnegative square root selected because $M_1$ is a magnitude. -/
theorem m1_eq_sqrt : m.M1 = Real.sqrt (m.M2 ^ 2 - m.M3 ^ 2 + m.M4 ^ 2) := by
  sorry

/-- The quantity under the root is nonnegative, as it must be for a physical
magnetization magnitude: $0 \le M_2^2 - M_3^2 + M_4^2$.
Carrier: `m1_sq` together with `M_nonneg .v1` ($0 \le M_1^2$). -/
theorem m1_sq_arg_nonneg : 0 ≤ m.M2 ^ 2 - m.M3 ^ 2 + m.M4 ^ 2 := by
  sorry

end CarnotMagnetizationModel

end IPhO2026.Problem3.C2

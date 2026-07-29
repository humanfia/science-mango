/-
IPhO 2026, Theoretical Problem 2 (Solar Cooker), Part B.1 — autoformalization.

Physical situation (Figure 2f, official source page `T2_page-3.png`). A
half-hollow-cylinder mirror of radius `R` (mirrored on the inside) is
illuminated by uniform parallel sunlight arriving along the mirror's optical
axis. A fully absorbing cylindrical container of radius `a` has its axis
parallel to the mirror axis; the container's centre lies `R / 2` from the
mirror centre on the system's symmetry plane. Every absorbed ray reflects
from the mirror at most once. `θ_max` is the maximum angle of incidence on
the mirror (measured against the normal at the point of incidence) among all
reflected rays striking the container, and `P₀` is the power the cylinder
would receive without the mirror.

Current subquestion (T2-B1): the container radius satisfies
`a = α * sin θ_max + β * sin (2 * θ_max)`; write `α` and `β` in terms of `R`.

Recorded official answer: `α = R` and `β = -R / 2` (kept strictly
conclusion-side in the target theorem; not fed into any structure field or
hypothesis).

This file is a by-`sorry` formalization: faithful declarations with proof
bodies left as `sorry`. (Proof status: all four proof obligations of this
redraft — `impactParam_eq_sin`, `sin_two_pos`,
`container_radius_at_extremal_angle`, `alpha_beta_in_terms_of_R` — are
currently closed with full proofs; the by-`sorry` discipline is kept in the
statement layer, which is unchanged.) The physics is modelled on a transverse
cross-section (the system is translationally invariant along the cylinder
axes), so points and direction vectors are pairs of real coordinates
carrying the dimension of length (directions are unit, hence dimensionless).

Cross-sectional frame (fixed by Figure 2f and cross-checked against the
official B.2/B.3 answers): mirror centre `C = (0, 0)`; the cross-sectional
image of the symmetry plane is the `y`-axis (the bisector of the
half-cylinder, perpendicular to the aperture diameter); the container
centre is `A = (0, -R / 2)`, i.e. `R / 2` from `C` along the symmetry axis
toward the mirrored belly (downstream of the sunlight); sunlight arrives
along direction `(0, -1)` onto the lower half-circle `y ≤ 0`, the open
aperture facing `y > 0`. The ray with impact parameter `x` strikes the
mirror at `(x, -√(R² - x²))`; by the symmetry of the configuration about
the `y`-axis the absorbed columns form a centred contiguous fan
`|x| ≤ x★`, whose extremal columns `±x★` are exactly the rays tangent to
the container circle. `θ_max = arcsin (x★ / R)`.

Governing physical laws (kept as hypotheses, never redefined locally):
specular reflection on the circular mirror profile (`reflection_law`),
absorption by the container disc (`absorbed_law`), the container-offset
geometry (`A_coord`), and the single-bounce contiguous-fan ray bookkeeping
(`no_gap`, `hit_branch`).

Key determinacy bridge: at an extremal column `x★` the reflected ray is
tangent to the container circle. `reflection_law` at column `x` is a
two-by-two linear system on the reflected-line scalars `(m x, b x)` with
nonzero determinant (the incoming axial ray is fully reversed in the
tangent direction by the circular-profile specular law), whose solution is
`b = -R² / (2 √(R² - x²))` — always negative with `|b| ≥ R / 2` — and the
tangency distance condition `|distToLine (line x) A| = a` then evaluates
(both mirror-image branches, via `|x|`) to the B.1 geometric identity
`a = R * sin θ_max - (R / 2) * sin (2 * θ_max)`. No sign branch is lost:
the signed-distance numerator `-R / 2 - b` is strictly positive for every
extremal column, so the absolute value resolves without extra case data.
The coefficient pair is then fixed because the given ansatz is a family
identity: the same `α, β` apply at the extremal angle of every cooker of
the same mirror radius (the later parts of the problem use exactly this),
and two distinct extremal angles give an invertible two-by-two linear
system for `(α - R, β + R / 2)`.
-/

import Mathlib

open Real Set

noncomputable section

namespace IPhO2026_2_B_1

/-- Points and vectors of the transverse cross-sectional plane: pairs of
real coordinates carrying the dimension of length. A plain pair type (not a
scalar alias) keeps the two-dimensional geometry of Figure 2f intact. -/
abbrev Vec : Type := ℝ × ℝ

/-- Euclidean norm of a cross-sectional vector; a length (or dimensionless
for unit direction vectors). -/
def vnorm (v : Vec) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

/-- Non-vertical lines `Y = m * X + b` in the cross-sectional plane: slope
`m` (dimensionless) and intercept `b` (a length). -/
structure Line2D where
  m : ℝ
  b : ℝ

/-- Signed distance from the point `q` to the line `r`: a length.
`distToLine r q = 0` means `q` lies on `r`. -/
def distToLine (r : Line2D) (q : Vec) : ℝ :=
  (q.2 - r.m * q.1 - r.b) / Real.sqrt (r.m ^ 2 + 1)

/-- Dimensionful parameters of the cooker of Figure 2f: mirror radius `R`
and container radius `a` (both lengths, hence positive). -/
structure CookerParams where
  R : ℝ
  a : ℝ
  hR : 0 < R
  ha : 0 < a

/-- Specular bookkeeping for the Figure-2f cooker: the parallel ray with
impact parameter `x` (its signed distance from the symmetry axis, a length)
strikes the half-cylinder mirror of radius `R` and the reflected
(non-vertical) line is recorded as `reflectedLine x`. All fields state
physical laws or figure readouts; none of them states the current
subquestion's coefficient answer. -/
structure CookerB1 (p : CookerParams) where
  /-- Mirror centre `C` of the cross-section. -/
  C : Vec
  /-- Container centre `A` of the cross-section. -/
  A : Vec
  /-- The Figure-2f frame: mirror centre at the origin; container centre on
  the symmetry axis (the cross-sectional image of the symmetry plane), at
  distance `R / 2` from `C` toward the mirrored belly. -/
  C_coord : C = (0, 0)
  A_coord : A = (0, -(p.R / 2))
  /-- The cross-sectional profile of the half-cylinder mirror: the half of
  the circle of radius `R` about `C` facing the incoming sunlight
  (`v.2 ≤ C.2`; the open aperture faces `v.2 > C.2`). -/
  mirrorSet : Set Vec
  mirrorSet_eq : mirrorSet =
    {v : Vec | vnorm (v.1 - C.1, v.2 - C.2) = p.R ∧ v.2 ≤ C.2}
  /-- The absorbing container cross-section: the closed disc of radius `a`
  about `A`. -/
  containerSet : Set Vec
  containerSet_eq : containerSet =
    {v : Vec | vnorm (v.1 - A.1, v.2 - A.2) ≤ p.a}
  /-- Reflected line `Y = (m x) * X + (b x)` of the absorbed ray with impact
  parameter `x`. Slopes and intercepts are records, not computed answers;
  the specular law below constrains them physically. -/
  reflectedLine : ℝ → Line2D
  /-- Impact parameters of the rays that are absorbed by the container
  after exactly one reflection at the mirror. -/
  hitSet : Set ℝ
  /-- Every absorbed ray reflects on the half-mirror arc: its mirror point
  has norm `R` on the sunlit half. -/
  on_mirror : ∀ x ∈ hitSet, (x, -Real.sqrt (p.R ^ 2 - x ^ 2)) ∈ mirrorSet
  /-- Law of specular reflection on the circular mirror profile (governing
  physical law, stated as incidence data rather than as a solved formula):
  the reflected line passes through the mirror point, and the specular
  reflection of the incoming axial direction `(0, -1)` in the tangent line
  at the mirror point `(x, y)`, `y = -√(R² - x²)` — the direction
  `(2 * x * y, y ^ 2 - x ^ 2)` — is a direction vector of the reflected
  line: `(2 * x * y) * m = y ^ 2 - x ^ 2`, here with the sign resolution
  `y = -√(R² - x²)` already applied. -/
  reflection_law : ∀ x ∈ hitSet,
    -Real.sqrt (p.R ^ 2 - x ^ 2) =
        (reflectedLine x).m * x + (reflectedLine x).b ∧
      (x ^ 2 - Real.sqrt (p.R ^ 2 - x ^ 2) ^ 2) =
        (reflectedLine x).m * (2 * x * Real.sqrt (p.R ^ 2 - x ^ 2))
  /-- Absorption law: every ray of the family reaches the container disc —
  its reflected line passes through `containerSet`. -/
  absorbed_law : ∀ x ∈ hitSet,
    ∃ q ∈ containerSet,
      q.2 = (reflectedLine x).m * q.1 + (reflectedLine x).b
  /-- Ray-family branch: all absorbed impact parameters lie inside the open
  aperture `(-R, R)`. -/
  hit_branch : ∀ x ∈ hitSet, x ∈ Set.Ioo (-p.R) p.R
  /-- The absorbed columns form a contiguous fan centred on the symmetry
  axis (Figure 2f is symmetric under `x ↦ -x`): no gaps between the axial
  ray and any absorbed ray. -/
  no_gap : ∀ x₁ x₂ : ℝ, x₁ ∈ hitSet → |x₂| ≤ |x₁| → x₂ ∈ hitSet

/-- Incidence angle of the ray with impact parameter `x` on the circular
mirror profile, measured against the radial normal at the mirror point:
`arcsin (|x| / R)`. Dimensionless. -/
def incidenceAngle (p : CookerParams) (x : ℝ) : ℝ :=
  Real.arcsin (|x| / p.R)

/-- Specification of `θ_max`: attained by a ray of the absorbed family,
bounding the incidence angles of all absorbed rays, and lying on the acute
branch `0 < θ_max < π / 2` seen in Figure 2f. -/
def IsThetaMax (p : CookerParams) (s : CookerB1 p) (θ : ℝ) : Prop :=
  θ ∈ Set.Ioo 0 (Real.pi / 2) ∧
    (∃ x ∈ s.hitSet, incidenceAngle p x = θ) ∧
      (∀ x ∈ s.hitSet, incidenceAngle p x ≤ θ)

/-- Inside the open aperture the impact-parameter magnitude is recovered
from the incidence angle as `|x| = R * sin θ`; the absolute value absorbs
the two mirror-image branches `±|x|` of Figure 2f. -/
lemma impactParam_eq_sin (p : CookerParams) {x θ : ℝ}
    (hx : x ∈ Set.Ioo (-p.R) p.R) (hθ : incidenceAngle p x = θ) :
    |x| = p.R * Real.sin θ := by
  have hR : 0 < p.R := p.hR
  have hlt : |x| / p.R < 1 := by
    rw [div_lt_one hR, abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hnn : 0 ≤ |x| / p.R := by positivity
  have h : Real.sin (incidenceAngle p x) = |x| / p.R := by
    unfold incidenceAngle
    rw [Real.sin_arcsin (by linarith) (by linarith)]
  calc |x| = p.R * (|x| / p.R) := by field_simp
    _ = p.R * Real.sin θ := by rw [← h, hθ]

/-- Positivity flashpoint for `sin (2 θ)` on the acute branch
`θ ∈ (0, π / 2)`, used to keep the coefficient identification
nondegenerate. -/
lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) := by
  have h2 : 2 * θ ∈ Set.Ioo 0 Real.pi :=
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact Real.sin_pos_of_mem_Ioo h2

/-- Extremality and tangency bookkeeping at a limiting ray (a ray attaining
`θ_max`). The extremal column belongs to the absorbed family, realizes the
extremal angle, is off the symmetry axis (the two mirror-image tangent
columns `±|x|` of Figure 2f, the absolute value in `incidenceAngle`
absorbing the branch), and its reflected line is tangent to the container
circle: it stays a signed-distance magnitude `a` from the container centre.
Together with `reflection_law` — a two-by-two linear system of nonzero
determinant — the tangency condition determines the container radius from
the extremal column, so this interface cannot be filled with arbitrary
line data. -/
structure ExtremalRaySpec (p : CookerParams) (s : CookerB1 p) (θ : ℝ) where
  x : ℝ
  hx : x ∈ s.hitSet
  hθ : incidenceAngle p x = θ
  /-- The extremal ray is off-axis: `θ_max > 0` columns are mirror-image
  pairs `±|x|` tangent to opposite silhouette generators of the container. -/
  off_axis : x ≠ 0
  /-- Tangency distance: the limiting reflected line passes exactly one
  container radius `a` from the container centre. -/
  tangent_dist : |distToLine (s.reflectedLine x) s.A| = p.a

/-- The given ansatz of the subquestion, in the sense the problem intends
and itself uses in the later parts (where `θ_max` varies with the container
size at fixed mirror radius `R`): one coefficient pair `α, β` expresses the
container radius at every extremal (tangent) configuration of the
Figure-2f cooker family of that same mirror radius. The real scalars `α, β`
parametrize the given ansatz — the specification never evaluates them. -/
def CoeffSpec (p : CookerParams) (α β : ℝ) : Prop :=
  ∀ (q : CookerParams), q.R = p.R → ∀ (s : CookerB1 q) (θ₁ : ℝ),
    IsThetaMax q s θ₁ →
    (∀ _e : ExtremalRaySpec q s θ₁, q.a = α * Real.sin θ₁ + β * Real.sin (2 * θ₁))

/-- A second extremal configuration in the same mirror-radius family: the
cooker family of Figure 2f contains configurations with a different
extremal angle (the later parts of the problem vary the container size at
fixed `R`). Its existence is a readout of the physical family, not of the
answer; it is what makes the coefficient pair of the given ansatz unique:
the identity holding at two distinct extremal angles cuts a two-by-two
linear system with determinant `2 * (cos θ' - cos θ) ≠ 0`. -/
structure SecondExtremalConfig (p : CookerParams) (θ' : ℝ) where
  q : CookerParams
  qR : q.R = p.R
  t : CookerB1 q
  hθ' : IsThetaMax q t θ'
  e' : ExtremalRaySpec q t θ'

/-- Tangency relation for the limiting ray (the B.1 geometric identity):
at an extremal angle `θ`, specular reflection at the mirror point
`(|x|, -√(R² - |x|²))` with `|x| = R * sin θ`, the container offset
`A = (0, -R / 2)`, and the tangency data of `ExtremalRaySpec` force the
container radius to be `a = R * sin θ - (R / 2) * sin (2 * θ)`.

This is the load-bearing bridge of the subquestion: its proof is the
two-by-two linear solve for `(m x, b x)` given by `reflection_law` at the
extremal column (determinant `-(2 * x) * (x ^ 2 + y ^ 2) ≠ 0`), giving
`b = -R ^ 2 / (2 * √(R² - x²))`, followed by the tangency distance
evaluation — where the signed-distance numerator `-R / 2 - b` is strictly
positive, so no sign branch is lost — and the double-angle elimination. -/
theorem container_radius_at_extremal_angle (p : CookerParams)
    (s : CookerB1 p) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (e : ExtremalRaySpec p s θ) :
    p.a = p.R * Real.sin θ - (p.R / 2) * Real.sin (2 * θ) := by
  have hR : 0 < p.R := p.hR
  have hRne : p.R ≠ 0 := ne_of_gt hR
  -- extremal-ray bookkeeping: the column lies in the open aperture and
  -- realizes the extremal angle
  have hx_hit : e.x ∈ s.hitSet := e.hx
  have hx_branch := s.hit_branch e.x hx_hit
  have hx_lt : |e.x| < p.R := by
    rw [abs_lt]
    exact ⟨by linarith [hx_branch.1], by linarith [hx_branch.2]⟩
  have hsin : |e.x| = p.R * Real.sin θ := impactParam_eq_sin p hx_branch e.hθ
  have hx_ne : e.x ≠ 0 := e.off_axis
  have hθ' : 0 < θ ∧ θ < Real.pi / 2 := hθ
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ'.2, Real.pi_pos], hθ'.2⟩
  -- mirror-point ordinate magnitude `y = √(R² - x²)`
  set y : ℝ := Real.sqrt (p.R ^ 2 - e.x ^ 2) with hy_def
  have hx2_lt : e.x ^ 2 < p.R ^ 2 := by
    have hsq : |e.x| ^ 2 < p.R ^ 2 := by nlinarith [abs_nonneg e.x, hx_lt, hR]
    rwa [sq_abs] at hsq
  have hy_sq : y ^ 2 = p.R ^ 2 - e.x ^ 2 := Real.sq_sqrt (by linarith)
  have hy_pos : 0 < y := Real.sqrt_pos.2 (by linarith)
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hR2pos : (0:ℝ) < p.R ^ 2 := sq_pos_of_pos hR
  -- the extreme column is off-axis, so the ordinate is strictly inside: `y < R`
  have hy_lt : y < p.R := by
    have hsq : y ^ 2 < p.R ^ 2 := by nlinarith [hy_sq, sq_pos_of_ne_zero hx_ne]
    have h2 : |y| < p.R := by
      by_contra hle
      push Not at hle
      have hself : p.R * p.R ≤ |y| * |y| := mul_self_le_mul_self hR.le hle
      rw [abs_of_pos hy_pos] at hself
      nlinarith [hsq, hself]
    rwa [abs_of_pos hy_pos] at h2
  -- trigonometric readout of the mirror point: `y = R cos θ`
  have hy_cos : y = p.R * Real.cos θ := by
    have hs1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    have hxabs : |e.x| ^ 2 = p.R ^ 2 * Real.sin θ ^ 2 := by
      rw [hsin]; ring
    have keqs : e.x ^ 2 = p.R ^ 2 * Real.sin θ ^ 2 := by
      calc e.x ^ 2 = |e.x| ^ 2 := by rw [sq_abs]
        _ = p.R ^ 2 * Real.sin θ ^ 2 := hxabs
    have hyc : y ^ 2 = (p.R * Real.cos θ) ^ 2 := by
      nlinarith [hy_sq, keqs, hs1]
    have hcases := sq_eq_sq_iff_eq_or_eq_neg.mp hyc
    rcases hcases with h | h
    · exact h
    · have hpos : (0:ℝ) < p.R * Real.cos θ := mul_pos hR hcos_pos
      linarith [h, hy_pos, hpos]
  -- the specular law at the extremal column: a two-by-two linear system on
  -- `(m, b)` with nonzero determinant `-(2 * x) * (x ^ 2 + y ^ 2)`
  obtain ⟨h_b, h_m⟩ := s.reflection_law e.x hx_hit
  rw [hy_sq] at h_m
  change -y = (s.reflectedLine e.x).m * e.x + (s.reflectedLine e.x).b at h_b
  set m : ℝ := (s.reflectedLine e.x).m with hm_def
  set b : ℝ := (s.reflectedLine e.x).b with hb_def
  have hxy_ne : (2:ℝ) * e.x * y ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hx_ne) hy_ne
  have hxy2 : (2 * e.x * y) ^ 2 ≠ 0 := pow_ne_zero 2 hxy_ne
  have hR4 : p.R ^ 4 = (2 * e.x ^ 2 - p.R ^ 2) ^ 2 + (2 * e.x * y) ^ 2 := by
    nlinarith [hy_sq]
  have hmx : m * (2 * e.x * y) = 2 * e.x ^ 2 - p.R ^ 2 := by
    nlinarith [h_m, hy_sq, h_b]
  have hm_eq : m = (2 * e.x ^ 2 - p.R ^ 2) / (2 * e.x * y) := by
    rw [← hmx]; field_simp
  have hb_eq : b = -p.R ^ 2 / (2 * y) := by
    have hbb : b = -y - m * e.x := by linarith [h_b]
    rw [hbb]
    have h2y : (2:ℝ) * y ≠ 0 := mul_ne_zero two_ne_zero hy_ne
    field_simp
    nlinarith [hmx, hy_sq]
  -- the line normalizer collapses exactly on the circle
  have hm2 : m ^ 2 + 1 = (p.R ^ 2 / (2 * e.x * y)) ^ 2 := by
    have key : ((2 * e.x ^ 2 - p.R ^ 2) ^ 2 / (2 * e.x * y) ^ 2 + 1)
        * (2 * e.x * y) ^ 2 = (p.R ^ 2) ^ 2 := by
      field_simp
      nlinarith [hR4]
    calc m ^ 2 + 1 = (2 * e.x ^ 2 - p.R ^ 2) ^ 2 / (2 * e.x * y) ^ 2 + 1 := by
          rw [hm_eq, div_pow]
      _ = (p.R ^ 2) ^ 2 / (2 * e.x * y) ^ 2 := by rw [eq_div_iff hxy2]; exact key
      _ = (p.R ^ 2 / (2 * e.x * y)) ^ 2 := by rw [div_pow]
  have hsval : Real.sqrt (m ^ 2 + 1) = p.R ^ 2 / (2 * |e.x| * y) := by
    rw [hm2, Real.sqrt_sq_eq_abs]
    have h1 : |p.R ^ 2| = p.R ^ 2 := abs_of_pos hR2pos
    have h2 : |(2:ℝ) * e.x * y| = 2 * |e.x| * y := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hy_pos]
    rw [abs_div, h1, h2]
  -- the intercept satisfies `b < -R / 2` strictly (since `x ≠ 0`)
  have hb_lt : b < -p.R / 2 := by
    rw [hb_eq]
    have h2y : (0:ℝ) < 2 * y := by linarith
    rw [div_lt_iff₀ h2y]
    have key : p.R * y < p.R * p.R := mul_lt_mul_of_pos_left hy_lt hR
    calc -p.R ^ 2 = -(p.R * p.R) := by ring
      _ < -(p.R * y) := by linarith [key]
      _ = (-p.R / 2) * (2 * y) := by ring
  -- hence the signed-distance numerator is strictly positive: the absolute
  -- value resolves without losing a sign branch
  have hnum_pos : (0:ℝ) < -p.R / 2 - b := by linarith
  -- evaluate the tangency distance at `A = (0, -R / 2)`
  have hA : s.A = (0, -(p.R / 2)) := s.A_coord
  have hnum : distToLine (s.reflectedLine e.x) s.A
      = (-p.R / 2 - b) / Real.sqrt (m ^ 2 + 1) := by
    unfold distToLine
    rw [hA]
    simp
    ring
  have hsqrt_pos : (0:ℝ) < Real.sqrt (m ^ 2 + 1) :=
    Real.sqrt_pos.2 (by positivity)
  have htan := e.tangent_dist
  rw [hnum, abs_of_pos (div_pos hnum_pos hsqrt_pos)] at htan
  have h_eq : p.a * Real.sqrt (m ^ 2 + 1) = -p.R / 2 - b := by
    rw [div_eq_iff (ne_of_gt hsqrt_pos)] at htan
    linarith [htan]
  rw [hsval, hb_eq] at h_eq
  -- clear denominators: `a * R = |x| * (R - y)`
  have h_mul : p.a * p.R = |e.x| * (p.R - y) := by
    have hax : (2:ℝ) * |e.x| * y ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (abs_ne_zero.mpr hx_ne)) hy_ne
    have h2y : (2:ℝ) * y ≠ 0 := mul_ne_zero two_ne_zero hy_ne
    have step1 : p.a * (p.R ^ 2 / (2 * |e.x| * y))
        = p.a * p.R ^ 2 / (2 * |e.x| * y) := by ring
    have step2 : -p.R / 2 - -p.R ^ 2 / (2 * y) = p.R * (p.R - y) / (2 * y) := by
      field_simp
      ring
    rw [step1, step2] at h_eq
    rw [div_eq_div_iff hax h2y] at h_eq
    have h2ne : (2:ℝ) ≠ 0 := two_ne_zero
    have hcan : p.a * p.R * (p.R * (2 * y)) = |e.x| * (p.R - y) * (p.R * (2 * y)) := by
      ring_nf at h_eq ⊢
      linarith [h_eq]
    exact mul_right_cancel₀ (mul_ne_zero hRne (mul_ne_zero h2ne hy_ne)) hcan
  -- substitute `|x| = R sin θ`, `y = R cos θ` and the double-angle formula
  rw [hsin, hy_cos] at h_mul
  have h1 : p.a = p.R * Real.sin θ * (1 - Real.cos θ) := by
    apply mul_right_cancel₀ hRne
    calc p.a * p.R = p.R * Real.sin θ * (p.R - p.R * Real.cos θ) := h_mul
      _ = (p.R * Real.sin θ * (1 - Real.cos θ)) * p.R := by ring
  rw [h1, Real.sin_two_mul]
  ring

/-- Main formalization target (T2-B1; blueprint
`thm:physics:IPhO_2026_2_B_1:target`). For the Figure-2f cooker with
extremal absorbed ray `e` at maximum incidence angle `θ_max`, the
coefficient pair `(α, β)` of the given family ansatz
`a = α * sin θ_max + β * sin (2 * θ_max)` is `α = R`, `β = -R / 2`.

Proof route: `container_radius_at_extremal_angle` at the configurations
`e` and `cfg₂.e'` gives the tangency identity at the two distinct extremal
angles `θ ≠ θ'`; `hcoef` at the same configurations gives the ansatz
there; subtraction yields
`(α - R) * sin θ' + (β + R / 2) * sin (2 θ') = 0` at both angles, a
two-by-two linear system in `(α - R, β + R / 2)` whose determinant
`2 * sin θ * sin θ' * (cos θ' - cos θ)` is nonzero by `strictAntiOn cos`
on `(0, π / 2)` — forcing the recorded values. The coefficient
identification is a conclusion, not an assumption. -/
theorem alpha_beta_in_terms_of_R (p : CookerParams) (s : CookerB1 p)
    {θ θ' α β : ℝ}
    (hθ : IsThetaMax p s θ) (hcoef : CoeffSpec p α β)
    (e : ExtremalRaySpec p s θ)
    (cfg₂ : SecondExtremalConfig p θ') (hdist : θ' ≠ θ) :
    α = p.R ∧ β = -p.R / 2 := by
  -- the tangency identity and the ansatz at the first extremal angle
  have hid₁ : p.a = p.R * Real.sin θ - (p.R / 2) * Real.sin (2 * θ) :=
    container_radius_at_extremal_angle p s hθ.1 e
  have hans₁ : p.a = α * Real.sin θ + β * Real.sin (2 * θ) :=
    hcoef p rfl s θ hθ e
  have heq₁ : (α - p.R) * Real.sin θ + (β + p.R / 2) * Real.sin (2 * θ) = 0 := by
    linarith [hid₁, hans₁]
  -- and at the second extremal configuration
  have hθ'' : θ' ∈ Set.Ioo 0 (Real.pi / 2) := cfg₂.hθ'.1
  have hid₂ : cfg₂.q.a = p.R * Real.sin θ' - (p.R / 2) * Real.sin (2 * θ') := by
    have h := container_radius_at_extremal_angle cfg₂.q cfg₂.t hθ'' cfg₂.e'
    rw [cfg₂.qR] at h
    exact h
  have hans₂ : cfg₂.q.a = α * Real.sin θ' + β * Real.sin (2 * θ') :=
    hcoef cfg₂.q cfg₂.qR cfg₂.t θ' cfg₂.hθ' cfg₂.e'
  have heq₂ : (α - p.R) * Real.sin θ' + (β + p.R / 2) * Real.sin (2 * θ') = 0 := by
    linarith [hid₂, hans₂]
  -- the two-by-two system for `(α - R, β + R / 2)` has nonzero determinant
  have hsθ : 0 < Real.sin θ := by
    apply Real.sin_pos_of_mem_Ioo
    exact ⟨hθ.1.1, by linarith [hθ.1.2, Real.pi_pos]⟩
  have hsθ' : 0 < Real.sin θ' := by
    apply Real.sin_pos_of_mem_Ioo
    exact ⟨hθ''.1, by linarith [hθ''.2, Real.pi_pos]⟩
  have hcos_ne : Real.cos θ' ≠ Real.cos θ := by
    intro hcos
    apply hdist
    have hsub : Set.Ioo 0 Real.pi ⊆ Set.Icc 0 Real.pi := Set.Ioo_subset_Icc_self
    exact Real.injOn_cos
      (hsub ⟨by linarith [hθ''.1], by linarith [hθ''.2, Real.pi_pos]⟩)
      (hsub ⟨by linarith [hθ.1.1], by linarith [hθ.1.2, Real.pi_pos]⟩) hcos
  have hdet : 2 * Real.sin θ * Real.sin θ' * (Real.cos θ' - Real.cos θ) ≠ 0 := by
    have hne1 : Real.sin θ ≠ 0 := ne_of_gt hsθ
    have hne2 : Real.sin θ' ≠ 0 := ne_of_gt hsθ'
    have hne3 : Real.cos θ' - Real.cos θ ≠ 0 := sub_ne_zero.mpr hcos_ne
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hne1) hne2) hne3
  rw [Real.sin_two_mul θ'] at heq₂
  rw [Real.sin_two_mul θ] at heq₁
  have hβ : β + p.R / 2 = 0 := by
    have key : (β + p.R / 2) * (2 * Real.sin θ * Real.sin θ'
        * (Real.cos θ' - Real.cos θ)) = 0 := by
      have hthis : ((α - p.R) * Real.sin θ'
          + (β + p.R / 2) * (2 * Real.sin θ' * Real.cos θ')) * Real.sin θ = 0 := by
        rw [heq₂]; ring
      have h1 : ((α - p.R) * Real.sin θ
          + (β + p.R / 2) * (2 * Real.sin θ * Real.cos θ)) * Real.sin θ' = 0 := by
        rw [heq₁]; ring
      have h2 : (β + p.R / 2) * (2 * Real.sin θ * Real.sin θ'
            * (Real.cos θ' - Real.cos θ))
          = ((α - p.R) * Real.sin θ'
              + (β + p.R / 2) * (2 * Real.sin θ' * Real.cos θ')) * Real.sin θ
            - ((α - p.R) * Real.sin θ
              + (β + p.R / 2) * (2 * Real.sin θ * Real.cos θ)) * Real.sin θ' := by ring
      rw [h2, hthis, h1]; ring
    exact (mul_eq_zero.mp key).resolve_right hdet
  have hα : α - p.R = 0 := by
    have hsθne : Real.sin θ ≠ 0 := ne_of_gt hsθ
    have hz : (α - p.R) * Real.sin θ = 0 := by
      rw [hβ] at heq₁
      ring_nf at heq₁ ⊢
      linarith [heq₁]
    exact (mul_eq_zero.mp hz).resolve_right hsθne
  constructor
  · linarith [hα]
  · linarith [hβ]

end IPhO2026_2_B_1

end

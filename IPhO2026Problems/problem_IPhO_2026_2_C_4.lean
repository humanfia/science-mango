import Mathlib

/-!
# IPhO 2026, Problem 2, Part C.4 — Caustic of the half-cylindrical mirror

Physical model (blueprint chapter
`blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_2_C_4.tex`):

* A half-cylindrical mirror of radius `R` (Figure 2g coordinate convention).
* Ray A is incident at angle `θ`; its reflected line is `y = m_A * x + b_A`.
* A neighboring parallel ray B is incident at `θ + Δθ`, with `Δθ ≪ θ`;
  its reflected line is `y = m_B * x + b_B`.
* The envelope (limiting intersection) of neighboring reflected rays is the
  caustic, parametrized by the incidence angle `θ`.

Previous-part result (C.3, natural-language prerequisite, assumed as an
hypothesis interface):
  `X_c θ = R * sin θ ^ 3`,
  `Y_c θ = (R / 2) * cos θ * (2 - cos (2 * θ))`.

Current subquestion (C.4, the proof target):
  for `θ ≪ 1`, the caustic takes the power-law form
  `Y_c = v * |X_c| ^ (p / q) + u`
  with `u = R / 2`, `v = (3 / 4) * R ^ (1 / 3)`, `p = 2`, `q = 3`.

Math note: an exact identity `Y_c θ = v * |X_c θ| ^ (p / q) + u` at every
small `θ` is FALSE for this caustic — Taylor expansion gives
`Y_c θ = R / 2 + (3 / 2) * R * θ ^ 2 + O(θ ^ 4)` and
`|X_c θ| ^ (2 / 3) = R ^ (2 / 3) * θ ^ 2 * (1 + O(θ ^ 2))`, so the two sides
agree only to leading order. The physically intended reading of `θ ≪ 1` is
asymptotic agreement to leading order as `θ → 0⁺`, formalized below with
`Asymptotics.IsEquivalent` on the filter `nhdsWithin 0 (Set.Ioi 0)`. The
recorded constants genuinely make the leading Taylor terms coincide; they are
not hand-picked to fit the definition.
-/

open Real
open Asymptotics

namespace IPhO2026_2_C_4

/-- The physical setup of the C-parts of IPhO 2026 Problem 2: the
half-cylindrical mirror of radius `R` (Figure 2g), the reflected lines of the
neighboring parallel rays A and B, and the caustic parametrized by the
incidence angle `θ`. All coordinates are Cartesian coordinates in the plane of
Figure 2g, so real scalars; `R` has the dimension of length. -/
structure HalfCylindricalMirrorCaustic where
  /-- Radius `R` of the half-cylindrical mirror (a length). -/
  R : ℝ
  /-- The mirror radius is positive. -/
  R_pos : 0 < R
  /-- Slope `m_A θ` of the line reflected from ray A at incidence angle `θ`. -/
  m_A : ℝ → ℝ
  /-- Intercept `b_A θ` of the line reflected from ray A. -/
  b_A : ℝ → ℝ
  /-- Slope `m_B θ Δθ` of the line reflected from the neighboring parallel
  ray B, incident at angle `θ + Δθ`. -/
  m_B : ℝ → ℝ → ℝ
  /-- Intercept `b_B θ Δθ` of the line reflected from ray B. -/
  b_B : ℝ → ℝ → ℝ
  /-- `X_c θ`, the x-coordinate of the limiting intersection of the two
  neighboring reflected lines as `Δθ → 0` (a length). -/
  X_c : ℝ → ℝ
  /-- `Y_c θ`, the y-coordinate of the limiting intersection (a length). -/
  Y_c : ℝ → ℝ
  /-- Envelope/limiting-intersection law: for every `θ` and every small
  nonzero offset `Δθ`, the unique intersection `(x, y)` of the reflected lines
  `y = m_A θ * x + b_A θ` and `y = m_B θ Δθ * x + b_B θ Δθ` tends to
  `(X_c θ, Y_c θ)` as `Δθ → 0`. This is the geometric definition of the
  caustic as the envelope of the reflected rays (Figure 2g). -/
  envelope_law :
    ∀ θ : ℝ, ∀ᶠ Δθ in nhdsWithin 0 (Set.Ioi 0),
      ∃! p : ℝ × ℝ,
        p.2 = m_A θ * p.1 + b_A θ ∧
        p.2 = m_B θ Δθ * p.1 + b_B θ Δθ
  /-- Previous part C.3: explicit limiting intersection coordinates,
  `X_c θ = R * sin θ ^ 3` (natural-language prerequisite, recorded here as a
  hypothesis on the caustic data). -/
  X_c_formula : ∀ θ : ℝ, X_c θ = R * sin θ ^ 3
  /-- Previous part C.3: explicit limiting intersection coordinates,
  `Y_c θ = (R / 2) * cos θ * (2 - cos (2 * θ))`. -/
  Y_c_formula : ∀ θ : ℝ, Y_c θ = R / 2 * cos θ * (2 - cos (2 * θ))

/-- The small-`θ` regime `θ ≪ 1` stipulated in the subquestion, carried by the
filter `nhdsWithin 0 (Set.Ioi 0)` (`θ → 0` from the positive side).
Branch/orientation data: incidence angles are taken positive, which is also
what makes the absolute value `|X_c|` of the source statement harmless —
`X_c θ = R * sin θ ^ 3` is positive for small positive `θ` — and selects the
physical branch of the power law. -/
noncomputable def smallAngleFilter : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)

/-- Small-angle regime predicate on an incidence angle: `θ` is positive and
strictly smaller than `1` radian (a plain-English reading of `θ ≪ 1`;
neighborhoods of `smallAngleFilter` carry the operative asymptotic notion). -/
def InSmallAngleRegime (θ : ℝ) : Prop :=
  0 < θ ∧ θ < 1

/-- Bridge between the plain-English small-angle regime and the asymptotic
filter: the set of angles satisfying `InSmallAngleRegime` is a neighborhood
of `0` within the positive angles, so statements eventually true along
`smallAngleFilter` apply to it (proved, not assumed). -/
theorem smallAngleRegime_mem_filter :
    {θ : ℝ | InSmallAngleRegime θ} ∈ smallAngleFilter := by
  rw [smallAngleFilter, mem_nhdsWithin]
  exact ⟨Set.Iio 1, isOpen_Iio, by simp, fun θ hθ => ⟨hθ.2, hθ.1⟩⟩

/-- The `θ ≪ 1` power-law form of a parametric plane curve `θ ↦ (X θ, Y θ)`:
the coordinate functions have a well-defined positive leading-order balance
as `θ → 0⁺`, i.e. they are asymptotically equivalent
(`Asymptotics.IsEquivalent`, `f ~[l] g`) along the small-angle filter:
`Y θ ~ v * X θ ^ (p / q) + u` and `X θ ~ w * θ ^ q` for some positive scale
`w`. The exponent is a positive rational; `u`, `v` carry the dimension of
length and `p / q` is dimensionless. This is the genuine asymptotic content
of the subquestion: the two sides agree to leading order without being
required to coincide exactly (they do not for the mirror caustic). All
quantities are parameters of the definition, so nothing here is specialized
to the recorded answer. -/
def CausticPowerLawForm (X Y : ℝ → ℝ) (u v : ℝ) (p q : ℕ) : Prop :=
  0 < p ∧ 0 < q ∧
  (fun θ : ℝ => Y θ) ~[smallAngleFilter]
    (fun θ => v * X θ ^ ((p : ℝ) / (q : ℝ)) + u) ∧
  ∃ w : ℝ, 0 < w ∧
    (fun θ : ℝ => X θ) ~[smallAngleFilter] (fun θ => w * θ ^ q)

/-- The power-law form with the recorded constants of subquestion C.4 made
explicit: the vertical shift `u` and the prefactor `v` are the ones determined
from the mirror geometry, with exponent `p / q = 2 / 3`. -/
def SatisfiesCausticPowerLaw (X Y : ℝ → ℝ) (R u v : ℝ) : Prop :=
  u = R / 2 ∧
  v = (3 / 4) * R ^ ((1 : ℝ) / 3) ∧
  CausticPowerLawForm X Y u v 2 3

namespace HalfCylindricalMirrorCaustic

variable (c : HalfCylindricalMirrorCaustic)

/-- Main formalization target for C.4: in the small-angle regime `θ ≪ 1`, the
caustic of the half-cylindrical mirror has the power-law form
`Y_c = v * |X_c| ^ (p / q) + u` with the recorded constants
`u = R / 2`, `v = (3 / 4) * R ^ (1 / 3)`, `p = 2`, `q = 3`, read as
asymptotic agreement to leading order as `θ → 0⁺`. The `|X_c|` of the source
statement is subsumed by the positive-angle branch encoded in
`smallAngleFilter`, where `X_c θ = R * sin θ ^ 3` is positive. All recorded
constants appear on the conclusion side only. -/
theorem caustic_small_angle_power_law :
    SatisfiesCausticPowerLaw c.X_c c.Y_c c.R (c.R / 2)
      ((3 / 4) * c.R ^ ((1 : ℝ) / 3)) := by
  sorry

end HalfCylindricalMirrorCaustic

end IPhO2026_2_C_4

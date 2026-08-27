import ArchonPhysics.CanonicalScalarIDSContinuity
import ArchonPhysics.CanonicalThresholdCountAlmostSureLimit

/-!
# Almost-sure compact-uniform convergence of canonical threshold counts

Fixed-threshold almost-sure convergence is first intersected over the
countable set of rational energies.  A deterministic finite-grid theorem
then upgrades convergence on this dense set to uniform convergence on every
compact real set: continuity supplies finitely many rational brackets with
small limiting oscillation, while monotonicity traps every approximating CDF
between its values at the bracket endpoints.

Applying the bridge to the canonical finite-volume harmonic counts gives
almost-sure uniform convergence to `canonicalScalarIDSValue` on the complete
physical spectral band `[0,5]`.
-/

namespace ArchonPhysics.CanonicalThresholdCountCompactUniformAlmostSureLimit

open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSContinuity
open ArchonPhysics.CanonicalThresholdCountAlmostSureLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open Filter MeasureTheory Set Topology

noncomputable section

/-- Simultaneous almost-sure convergence at every rational threshold. -/
theorem canonicalNormalizedHarmonicThresholdCount_tendsto_scalarIDS_rat_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      ∀ q : Rat,
        Tendsto
          (fun n : Nat ↦
            canonicalNormalizedHarmonicThresholdCount (n + 1) (q : Real) omega)
          atTop (nhds (canonicalScalarIDSValue (q : Real))) := by
  exact ae_all_iff.mpr fun q ↦
    canonicalNormalizedHarmonicThresholdCount_tendsto_scalarIDS_ae (q : Real)

/-- Continuity supplies rational brackets around one point whose limiting
function values differ by less than a prescribed tolerance. -/
theorem exists_rat_bracket_of_continuous
    (g : Real → Real) (hg : Continuous g) (x : Real)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ l r : Rat, (l : Real) < x ∧ x < (r : Real) ∧
      g (r : Real) - g (l : Real) < epsilon := by
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp hg.continuousAt)
      (epsilon / 2) (by positivity)
  obtain ⟨l, hxl, hlx⟩ := exists_rat_btwn (sub_lt_self x hdelta)
  obtain ⟨r, hxr, hrx⟩ := exists_rat_btwn (lt_add_of_pos_right x hdelta)
  have hldist : dist (l : Real) x < delta := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hrdist : dist (r : Real) x < delta := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hlcontrol := hcontrol hldist
  have hrcontrol := hcontrol hrdist
  rw [Real.dist_eq] at hlcontrol hrcontrol
  exact ⟨l, r, hlx, hxr, by
    rcases abs_lt.mp hlcontrol with ⟨hlower, hupper⟩
    rcases abs_lt.mp hrcontrol with ⟨rlower, rupper⟩
    linarith⟩

/-- On a compact real set, continuity produces finitely many rational
brackets with uniformly small oscillation of the limiting function. -/
theorem exists_finite_rat_brackets_of_compact
    (g : Real → Real) (hg : Continuous g)
    (S : Set Real) (hS : IsCompact S)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ t : Finset (Rat × Rat),
      ∀ x ∈ S, ∃ p ∈ t,
        (p.1 : Real) < x ∧ x < (p.2 : Real) ∧
          g (p.2 : Real) - g (p.1 : Real) < epsilon := by
  have hbracket : ∀ x : S, ∃ l r : Rat,
      (l : Real) < x.1 ∧ x.1 < (r : Real) ∧
        g (r : Real) - g (l : Real) < epsilon := by
    intro x
    exact exists_rat_bracket_of_continuous g hg x.1 hepsilon
  choose lower upper hlower hupper hgap using hbracket
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover
    (fun x : S ↦ Ioo (lower x : Real) (upper x : Real))
    (fun _ ↦ isOpen_Ioo) (by
      intro x hx
      rw [mem_iUnion]
      exact ⟨⟨x, hx⟩, hlower ⟨x, hx⟩, hupper ⟨x, hx⟩⟩)
  refine ⟨s.image (fun x ↦ (lower x, upper x)), ?_⟩
  intro x hx
  rcases mem_iUnion₂.mp (hs hx) with ⟨i, hi, hxi⟩
  refine ⟨(lower i, upper i), Finset.mem_image.mpr ⟨i, hi, rfl⟩,
    hxi.1, hxi.2, hgap i⟩

/-- Deterministic dense-grid bridge for monotone CDFs.  If every approximant
and the continuous limit are monotone, convergence at all rational points is
uniform on every compact set. -/
theorem tendstoUniformlyOn_of_monotone_of_rat_tendsto
    (F : Nat → Real → Real) (g : Real → Real)
    (hF : ∀ n, Monotone (F n)) (hgmono : Monotone g)
    (hgcontinuous : Continuous g)
    (hpoint : ∀ q : Rat,
      Tendsto (fun n ↦ F n (q : Real)) atTop (nhds (g (q : Real))))
    (S : Set Real) (hS : IsCompact S) :
    TendstoUniformlyOn F g atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  obtain ⟨t, ht⟩ := exists_finite_rat_brackets_of_compact
    g hgcontinuous S hS (show 0 < epsilon / 2 by positivity)
  have hendpoint : ∀ p ∈ t,
      ∀ᶠ n : Nat in atTop,
        dist (F n (p.1 : Real)) (g (p.1 : Real)) < epsilon / 2 ∧
        dist (F n (p.2 : Real)) (g (p.2 : Real)) < epsilon / 2 := by
    intro p hp
    have hleft : ∀ᶠ n : Nat in atTop,
        dist (F n (p.1 : Real)) (g (p.1 : Real)) < epsilon / 2 := by
      rw [eventually_atTop]
      exact Metric.tendsto_atTop.mp (hpoint p.1) (epsilon / 2) (by positivity)
    have hright : ∀ᶠ n : Nat in atTop,
        dist (F n (p.2 : Real)) (g (p.2 : Real)) < epsilon / 2 := by
      rw [eventually_atTop]
      exact Metric.tendsto_atTop.mp (hpoint p.2) (epsilon / 2) (by positivity)
    exact hleft.and hright
  filter_upwards [(Filter.eventually_all_finset t).mpr hendpoint] with n hn
  intro x hx
  obtain ⟨p, hp, hpx, hxp, hgap⟩ := ht x hx
  have hFleft : F n (p.1 : Real) ≤ F n x := hF n hpx.le
  have hFright : F n x ≤ F n (p.2 : Real) := hF n hxp.le
  have hgleft : g (p.1 : Real) ≤ g x := hgmono hpx.le
  have hgright : g x ≤ g (p.2 : Real) := hgmono hxp.le
  have hleft := (hn p hp).1
  have hright := (hn p hp).2
  rw [Real.dist_eq] at hleft hright ⊢
  rcases abs_lt.mp hleft with ⟨hleftLower, hleftUpper⟩
  rcases abs_lt.mp hright with ⟨hrightLower, hrightUpper⟩
  apply abs_lt.mpr
  constructor <;> linarith

/-- Almost surely, the full finite-volume canonical harmonic CDF converges
uniformly to the deterministic scalar IDS on the physical spectral band
`[0,5]`. -/
theorem canonicalNormalizedHarmonicThresholdCount_tendstoUniformlyOn_Icc_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      TendstoUniformlyOn
        (fun n : Nat ↦ fun E : Real ↦
          canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
        canonicalScalarIDSValue atTop (Icc (0 : Real) 5) := by
  filter_upwards
    [canonicalNormalizedHarmonicThresholdCount_tendsto_scalarIDS_rat_ae]
      with omega hrat
  exact tendstoUniformlyOn_of_monotone_of_rat_tendsto
    (fun n : Nat ↦ fun E : Real ↦
      canonicalNormalizedHarmonicThresholdCount (n + 1) E omega)
    canonicalScalarIDSValue
    (fun n ↦ monotone_canonicalNormalizedHarmonicThresholdCount (n + 1) omega)
    monotone_canonicalScalarIDSValue
    continuous_canonicalScalarIDSValue hrat (Icc (0 : Real) 5) isCompact_Icc

end

end ArchonPhysics.CanonicalThresholdCountCompactUniformAlmostSureLimit

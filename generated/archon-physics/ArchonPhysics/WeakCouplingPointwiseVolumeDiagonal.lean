import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Diagonal weak-coupling selection from fixed-volume limits

Pointwise convergence at every finite volume does not provide a rate uniform
in the volume.  It does, however, give an honest diagonal statement: one can
choose a positive coupling `g n -> 0` slowly enough that the error at volume
`n` also tends to zero.  This module records exactly that implication and no
stronger joint-limit claim.

The selected sequence may depend on the entire family of finite-volume
limits.  In particular, this theorem does not produce a power law relating
`g` and `n`; such a law still requires uniform chart/RPA/recollision costs.
-/

namespace ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal

open Filter Set
open scoped Topology

noncomputable section

/-- A family which tends to zero as `g -> 0+` at each fixed natural index
admits a positive diagonal coupling tending to zero along which the indexed
errors tend to zero.  Both coupling and error are explicitly bounded by
`1 / (n + 1)`. -/
theorem exists_positive_diagonal_of_pointwise_nhdsGT_zero
    (error : Nat -> Real -> Real)
    (hpointwise : forall n,
      Tendsto (error n) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    exists coupling : Nat -> Real,
      (forall n, 0 < coupling n) ∧
      (forall n, coupling n < 1 / ((n : Real) + 1)) ∧
      (forall n, |error n (coupling n)| < 1 / ((n : Real) + 1)) ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto (fun n => error n (coupling n)) atTop (nhds 0) := by
  have hexists : forall n : Nat, exists g : Real,
      0 < g ∧ g < 1 / ((n : Real) + 1) ∧
        |error n g| < 1 / ((n : Real) + 1) := by
    intro n
    let epsilon : Real := 1 / ((n : Real) + 1)
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      positivity
    have herror : {g : Real | |error n g| < epsilon} ∈
        nhdsWithin 0 (Ioi 0) := by
      have hball : Metric.ball (0 : Real) epsilon ∈ nhds (0 : Real) :=
        Metric.ball_mem_nhds 0 hepsilon
      have hevent := (hpointwise n).eventually hball
      filter_upwards [hevent] with g hg
      simpa [Real.dist_eq] using hg
    have hupper : Iio epsilon ∈ nhdsWithin (0 : Real) (Ioi 0) := by
      exact (inf_le_left : nhdsWithin (0 : Real) (Ioi 0) <= nhds 0)
        (Iio_mem_nhds hepsilon)
    have hpositive : Ioi (0 : Real) ∈ nhdsWithin 0 (Ioi 0) :=
      self_mem_nhdsWithin
    have hcombined :
        {g : Real | |error n g| < epsilon} ∩ (Iio epsilon ∩ Ioi 0) ∈
          nhdsWithin 0 (Ioi 0) :=
      inter_mem herror (inter_mem hupper hpositive)
    obtain ⟨g, hgError, hgUpper, hgPositive⟩ :=
      Filter.nonempty_of_mem hcombined
    exact ⟨g, hgPositive, hgUpper, hgError⟩
  choose coupling hpositive hupper herror using hexists
  have hrate : Tendsto (fun n : Nat => 1 / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcoupling : Tendsto coupling atTop (nhds 0) :=
    squeeze_zero (fun n => (hpositive n).le)
      (fun n => (hupper n).le) hrate
  have herrorLimit : Tendsto (fun n => error n (coupling n))
      atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 <|
      squeeze_zero (fun n => abs_nonneg (error n (coupling n)))
        (fun n => (herror n).le) hrate
  exact ⟨coupling, hpositive, hupper, herror, hcoupling, herrorLimit⟩

end

end ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal

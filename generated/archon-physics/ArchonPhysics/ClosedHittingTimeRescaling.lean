import ArchonPhysics.HittingTimeStability
import ArchonPhysics.ThermalizationTransfer

/-!
# Exact rescaling of closed-threshold hitting times

Positive finite multiplication is an order automorphism of `ENNReal`, so it
maps the infimum of all strictly positive event times to the infimum of the
rescaled event times.  This argument retains `⊤` exactly when the event never
occurs; no conversion of an extended time to a real number is used.
-/

namespace ArchonPhysics

open scoped ENNReal

noncomputable section

/-- Transport a first hitting time through any order automorphism of extended
nonnegative time.  Positivity is preserved because an order isomorphism maps
the bottom element to the bottom element. -/
theorem firstHittingTime_comp_orderIso_symm
    (A : ENNReal → Prop) (e : ENNReal ≃o ENNReal) :
    e (HittingTime.firstHittingTime A) =
      HittingTime.firstHittingTime (fun t => A (e.symm t)) := by
  unfold HittingTime.firstHittingTime
  rw [map_sInf]
  congr 1
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ?_⟩
    · change (⊥ : ENNReal) < e s
      rw [← OrderIso.map_bot e]
      exact e.lt_iff_lt.mpr hs.1
    · simpa using hs.2
  · intro ht
    refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
    refine ⟨?_, ?_⟩
    · change (⊥ : ENNReal) < e.symm t
      rw [← OrderIso.map_bot e.symm]
      exact e.symm.lt_iff_lt.mpr ht.1
    · simpa using ht.2

/-- Rescaling real observation time by a positive factor rescales the true
closed-threshold `ENNReal` hitting time by exactly the same factor. -/
theorem distanceThresholdHittingTime_timeScale
    (distance : Real → Real) (delta c : Real) (hc : 0 < c) :
    ENNReal.ofReal c * distanceThresholdHittingTime distance delta =
      distanceThresholdHittingTime (fun t => distance (t / c)) delta := by
  let cE : ENNReal := ENNReal.ofReal c
  have hcE0 : cE ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
  have hcEtop : cE ≠ ⊤ := ENNReal.ofReal_ne_top
  let e : ENNReal ≃o ENNReal :=
    ENNReal.mulLeftOrderIso cE (ENNReal.isUnit_iff.mpr ⟨hcE0, hcEtop⟩)
  have h := firstHittingTime_comp_orderIso_symm
    (distanceThresholdEvent distance delta) e
  have htime (t : ENNReal) : (e.symm t).toReal = t.toReal / c := by
    have happly := e.apply_symm_apply t
    change cE * e.symm t = t at happly
    have hreal := congrArg ENNReal.toReal happly
    rw [ENNReal.toReal_mul] at hreal
    dsimp only [cE] at hreal
    rw [ENNReal.toReal_ofReal hc.le] at hreal
    apply (eq_div_iff (ne_of_gt hc)).2
    rw [mul_comm]
    exact hreal
  have hevent :
      (fun t => distanceThresholdEvent distance delta (e.symm t)) =
        distanceThresholdEvent (fun t => distance (t / c)) delta := by
    funext t
    apply propext
    simp only [distanceThresholdEvent, htime]
  unfold distanceThresholdHittingTime
  rw [← hevent]
  simpa [e, cE] using h

/-- The kinetic specialization: for nonzero coupling, `g² T_eq` is exactly
the first threshold time of the microscopic distance observed at `tau / g²`.
-/
theorem distanceThresholdHittingTime_kineticScale
    (distance : Real → Real) (delta g : Real) (hg : g ≠ 0) :
    ENNReal.ofReal (g ^ 2) *
        distanceThresholdHittingTime distance delta =
      distanceThresholdHittingTime
        (fun tau => distance (tau / g ^ 2)) delta := by
  exact distanceThresholdHittingTime_timeScale distance delta (g ^ 2)
    (sq_pos_of_ne_zero hg)

/-- Adapter to the generic probabilistic-transfer definition.  Once a model's
unscaled equilibration time is identified with its true closed hit, the
scaled-hitting identification is automatic and still preserves `⊤`. -/
theorem ThermalizationTransfer.scaledEquilibrationTime_eq_hittingTime_of_eq
    {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (N : Nat) (g : Real) (omega : Omega)
    (distance : Real → Real) (delta : Real) (hg : g ≠ 0)
    (hidentification : equilibrationTime N g omega =
      distanceThresholdHittingTime distance delta) :
    scaledEquilibrationTime equilibrationTime N g omega =
      distanceThresholdHittingTime
        (fun tau => distance (tau / g ^ 2)) delta := by
  rw [scaledEquilibrationTime, hidentification]
  exact distanceThresholdHittingTime_kineticScale distance delta g hg

end

end ArchonPhysics

import ArchonPhysics.EquipartitionEntropy

/-!
# Stability of normalized finite modal-energy profiles

The thermalization observable normalizes a finite nonnegative energy profile
by its total mass.  This module isolates the deterministic estimate needed by
the microscopic-to-kinetic limit: unnormalized `l1` control and a positive
lower bound on total energy imply normalized `l1` control.

No microscopic convergence or kinetic limit is asserted here.
-/

namespace ArchonPhysics.NormalizedL1Stability

open ArchonPhysics.EquipartitionEntropy
open Filter

noncomputable section

/-- The error in total mass is bounded by the finite `l1` error. -/
theorem abs_totalWeight_sub_le_l1Distance {ι : Type} [Fintype ι]
    (w v : ι → Real) :
    |totalWeight w - totalWeight v| ≤ l1Distance w v := by
  unfold totalWeight l1Distance
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Coordinatewise normalization error, with the denominator variation
shown explicitly. -/
theorem abs_normalizedWeights_sub_le {ι : Type} [Fintype ι]
    (w v : ι → Real) (i : ι)
    (hwTotal : 0 < totalWeight w) (hvTotal : 0 < totalWeight v)
    (hv : 0 ≤ v i) :
    |normalizedWeights w i - normalizedWeights v i| ≤
      |w i - v i| / totalWeight w +
        v i * |totalWeight v - totalWeight w| /
          (totalWeight w * totalWeight v) := by
  have hwne : totalWeight w ≠ 0 := ne_of_gt hwTotal
  have hvne : totalWeight v ≠ 0 := ne_of_gt hvTotal
  have hmulpos : 0 < totalWeight w * totalWeight v :=
    mul_pos hwTotal hvTotal
  have hdecomp :
      normalizedWeights w i - normalizedWeights v i =
        (w i - v i) / totalWeight w +
          v i * (totalWeight v - totalWeight w) /
            (totalWeight w * totalWeight v) := by
    unfold normalizedWeights
    field_simp [hwne, hvne]
    ring
  rw [hdecomp]
  calc
    |(w i - v i) / totalWeight w +
        v i * (totalWeight v - totalWeight w) /
          (totalWeight w * totalWeight v)| ≤
        |(w i - v i) / totalWeight w| +
          |v i * (totalWeight v - totalWeight w) /
            (totalWeight w * totalWeight v)| := abs_add_le _ _
    _ = |w i - v i| / totalWeight w +
        v i * |totalWeight v - totalWeight w| /
          (totalWeight w * totalWeight v) := by
      simp only [abs_div, abs_mul, abs_of_pos hwTotal,
        abs_of_nonneg hv, abs_of_pos hmulpos]

/-- Normalization is quantitatively stable in finite `l1`: if `v` is
nonnegative and both totals are positive, the normalized error is at most
twice the raw error divided by the total of `w`. -/
theorem l1Distance_normalizedWeights_le {ι : Type} [Fintype ι]
    (w v : ι → Real)
    (hwTotal : 0 < totalWeight w) (hvTotal : 0 < totalWeight v)
    (hv : ∀ i, 0 ≤ v i) :
    l1Distance (normalizedWeights w) (normalizedWeights v) ≤
      2 * l1Distance w v / totalWeight w := by
  have hwne : totalWeight w ≠ 0 := ne_of_gt hwTotal
  have hvne : totalWeight v ≠ 0 := ne_of_gt hvTotal
  have hdenom_nonneg :
      0 ≤ totalWeight w * totalWeight v :=
    (mul_pos hwTotal hvTotal).le
  have htotal :
      |totalWeight v - totalWeight w| ≤ l1Distance w v := by
    simpa only [abs_sub_comm] using
      abs_totalWeight_sub_le_l1Distance w v
  calc
    l1Distance (normalizedWeights w) (normalizedWeights v) =
        ∑ i, |normalizedWeights w i - normalizedWeights v i| := rfl
    _ ≤ ∑ i, (|w i - v i| / totalWeight w +
        v i * |totalWeight v - totalWeight w| /
          (totalWeight w * totalWeight v)) :=
      Finset.sum_le_sum fun i _ ↦
        abs_normalizedWeights_sub_le w v i hwTotal hvTotal (hv i)
    _ ≤ ∑ i, (|w i - v i| / totalWeight w +
        v i * l1Distance w v /
          (totalWeight w * totalWeight v)) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hv i
    _ = 2 * l1Distance w v / totalWeight w := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_div, ← Finset.sum_mul]
      change
        l1Distance w v / totalWeight w +
            totalWeight v * l1Distance w v /
              (totalWeight w * totalWeight v) =
          2 * l1Distance w v / totalWeight w
      field_simp [hwne, hvne]
      ring

/-- A uniform positive lower bound on the reference total gives a denominator-
free Lipschitz estimate convenient for convergence arguments. -/
theorem l1Distance_normalizedWeights_le_of_lowerBound
    {ι : Type} [Fintype ι]
    (w v : ι → Real) {energyFloor : Real}
    (hfloor : 0 < energyFloor)
    (hwFloor : energyFloor ≤ totalWeight w)
    (hvTotal : 0 < totalWeight v)
    (hv : ∀ i, 0 ≤ v i) :
    l1Distance (normalizedWeights w) (normalizedWeights v) ≤
      (2 / energyFloor) * l1Distance w v := by
  have hwTotal : 0 < totalWeight w := hfloor.trans_le hwFloor
  calc
    l1Distance (normalizedWeights w) (normalizedWeights v) ≤
        2 * l1Distance w v / totalWeight w :=
      l1Distance_normalizedWeights_le w v hwTotal hvTotal hv
    _ ≤ (2 / energyFloor) * l1Distance w v := by
      have hinv : (totalWeight w)⁻¹ ≤ energyFloor⁻¹ :=
        (inv_le_inv₀ hwTotal hfloor).2 hwFloor
      have herr : 0 ≤ l1Distance w v := by
        unfold l1Distance
        positivity
      calc
        2 * l1Distance w v / totalWeight w =
            (2 * (totalWeight w)⁻¹) * l1Distance w v := by ring
        _ ≤ (2 * energyFloor⁻¹) * l1Distance w v := by
          gcongr
        _ = (2 / energyFloor) * l1Distance w v := by ring

/-- Raw finite-profile `l1` convergence plus a uniform positive total-energy
floor implies convergence of the normalized profiles. -/
theorem tendsto_l1Distance_normalizedWeights_zero
    {ι : Type} [Fintype ι]
    (w v : Nat → ι → Real) {energyFloor : Real}
    (hfloor : 0 < energyFloor)
    (hwFloor : ∀ n, energyFloor ≤ totalWeight (w n))
    (hvTotal : ∀ n, 0 < totalWeight (v n))
    (hv : ∀ n i, 0 ≤ v n i)
    (hraw : Tendsto (fun n ↦ l1Distance (w n) (v n)) atTop (nhds 0)) :
    Tendsto
      (fun n ↦ l1Distance (normalizedWeights (w n))
        (normalizedWeights (v n)))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    unfold l1Distance
    positivity
  · intro n
    exact l1Distance_normalizedWeights_le_of_lowerBound (w n) (v n)
      hfloor (hwFloor n) (hvTotal n) (hv n)
  · simpa using
      (tendsto_const_nhds.mul hraw :
        Tendsto (fun n ↦ (2 / energyFloor) * l1Distance (w n) (v n))
          atTop (nhds ((2 / energyFloor) * 0)))

end

end ArchonPhysics.NormalizedL1Stability

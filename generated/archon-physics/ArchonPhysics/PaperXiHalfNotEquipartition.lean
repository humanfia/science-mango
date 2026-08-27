import ArchonPhysics.PaperSpectralEntropyCriterion

/-!
# The paper half-threshold does not imply full-mode equipartition

This is a static diagnostic counterexample.  On two modes, monitor only the
second mode and give the full system energies in the ratio `3 : 1`.  The
monitored singleton is internally entropy-maximal and carries one quarter of
the total energy, so the complete paper observable is exactly `1 / 2`.
Nevertheless the normalized full energy profile is `(3/4, 1/4)`, whose
`l1` distance from the uniform profile is `1 / 2`.

No trajectory is constructed here.  In particular, this does not claim that
the specific numerical trajectories in Wang--Fu--Zhang--Zhao realize this
profile; it only proves that the scalar threshold by itself cannot logically
imply exact, or arbitrarily accurate, full-mode equipartition.
-/

namespace ArchonPhysics.PaperXiHalfNotEquipartition

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.PaperSpectralEntropyCriterion
open scoped BigOperators

noncomputable section

/-- The monitored upper singleton is mode `1`. -/
def monitored : Finset (Fin 2) := {1}

/-- Full two-mode energy profile: unmonitored energy `3`, monitored energy `1`. -/
def energy : Fin 2 -> Real := ![3, 1]

theorem totalWeight_energy : totalWeight energy = 4 := by
  norm_num [totalWeight, energy, Fin.sum_univ_succ]


theorem monitoredBandEnergyFactor_energy_eq_half :
    monitoredBandEnergyFactor energy monitored = 1 / 2 := by
  unfold monitoredBandEnergyFactor
  rw [totalWeight_energy]
  norm_num [monitored, energy]


theorem monitored_subsingleton (i j : monitored) : i = j := by
  apply Subtype.ext
  have hi : (i : Fin 2) = 1 := by
    simpa [monitored] using i.property
  have hj : (j : Fin 2) = 1 := by
    simpa [monitored] using j.property
  exact hi.trans hj.symm

theorem normalizedMonitoredWeights_eq_one :
    normalizedWeights (monitoredBandWeights energy monitored) =
      fun _ => 1 := by
  have hvalue (i : monitored) :
      monitoredBandWeights energy monitored i = 1 := by
    have hi : (i : Fin 2) = 1 := by
      simpa [monitored] using i.property
    change energy (i : Fin 2) = 1
    rw [hi]
    rfl
  have htotal :
      totalWeight (monitoredBandWeights energy monitored) = 1 := by
    let one : monitored := ⟨1, by simp [monitored]⟩
    unfold totalWeight
    calc
      (∑ i, monitoredBandWeights energy monitored i) =
          monitoredBandWeights energy monitored one :=
        Fintype.sum_eq_single one fun i hi =>
          (hi (monitored_subsingleton i one)).elim
      _ = 1 := hvalue one
  funext i
  rw [normalizedWeights, htotal, hvalue]
  norm_num

theorem monitoredSingleton_effectiveModeFraction_eq_one :
    normalizedEffectiveModeFraction
        (normalizedWeights (monitoredBandWeights energy monitored)) = 1 := by
  rw [normalizedMonitoredWeights_eq_one]
  simp [normalizedEffectiveModeFraction, participationNumber, spectralEntropy,
    monitored]

/-- The paper diagnostic reaches its published half threshold. -/
theorem paperXi_energy_eq_half :
    paperXi energy monitored = 1 / 2 := by
  rw [paperXi]
  rw [monitoredBandEnergyFactor_energy_eq_half,
    monitoredSingleton_effectiveModeFraction_eq_one]
  norm_num


/-- The same profile remains a macroscopic distance from full equipartition. -/
theorem normalizedWeights_energy_eq :
    normalizedWeights energy = ![(3 : Real) / 4, 1 / 4] := by
  funext i
  rw [normalizedWeights, totalWeight_energy]
  fin_cases i <;> norm_num [energy]

theorem fullMode_l1Distance_eq_half :
    l1Distance (normalizedWeights energy)
      (uniformWeights : Fin 2 -> Real) = 1 / 2 := by
  rw [normalizedWeights_energy_eq]
  norm_num [l1Distance, uniformWeights, Fin.sum_univ_succ]

/-- Combined counterexample: `paperXi = 1/2` coexists with full-mode `l1`
error `1/2`, so every requested accuracy below `1/2` fails. -/
theorem exists_paperXi_half_with_fullMode_error_half :
    paperXi energy monitored = 1 / 2 ∧
      l1Distance (normalizedWeights energy)
        (uniformWeights : Fin 2 -> Real) = 1 / 2 :=
  ⟨paperXi_energy_eq_half, fullMode_l1Distance_eq_half⟩

end

end ArchonPhysics.PaperXiHalfNotEquipartition

import ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence

/-!
# Consumer: arbitrarily long microscopic--kinetic persistence

This consumer kernel-locks the distinction between a fixed finite-window
microscopic--kinetic estimate and an expanding-window thermodynamic limit.  It
does not assert permanent convergence of a fixed finite Hamiltonian orbit.
-/

namespace ArchonPhysicsConsumers.Thermalization.ArbitrarilyLongMicroscopicKineticPersistence

open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence

/-- Kernel-lock that a numerical first hit can only precede the sustained
persistent equilibration time. -/
theorem problem_first_hit_le_persistent_equipartition_time :
    (@microscopicFirstEquipartitionTime_le_persistentEquipartitionTime) =
      @microscopicFirstEquipartitionTime_le_persistentEquipartitionTime := rfl

/-- Kernel-lock agreement with the numerical first-hit convention when that
first hit itself carries a positive finite persistent tail. -/
theorem problem_first_hit_eq_persistent_of_first_hit_persists :
    (@microscopicFirstEquipartitionTime_eq_persistent_of_firstHit_persists) =
      @microscopicFirstEquipartitionTime_eq_persistent_of_firstHit_persists := rfl

/-- Kernel-lock fixed-window transfer from microscopic--kinetic approximation
to microscopic equilibrium. -/
theorem problem_fixed_window_microscopic_kinetic_transfer :
    (@microscopicEquilibriumWindowBadProbability_tendsto_zero) =
      @microscopicEquilibriumWindowBadProbability_tendsto_zero := rfl

/-- Kernel-lock construction of a horizon-dependent cutoff from fixed-horizon
equilibrium convergence. -/
theorem problem_exists_sizeCutoff_for_equilibrium_expanding_windows :
    (@exists_sizeCutoff_for_equilibrium_expanding_windows) =
      @exists_sizeCutoff_for_equilibrium_expanding_windows := rfl

/-- Kernel-lock the direct long-time microscopic--kinetic diagonal transfer. -/
theorem problem_expanding_window_microscopic_kinetic_transfer :
    (@equilibriumWindowBadProbability_tendsto_zero_along_expanding_windows_of_kinetic) =
      @equilibriumWindowBadProbability_tendsto_zero_along_expanding_windows_of_kinetic := rfl


/-- Kernel-lock the joint shrinking-error, expanding-duration thermodynamic
persistence transfer. -/
theorem problem_joint_strict_thermodynamic_persistence :
    (@equilibriumBadProbability_and_threshold_tendsto_zero_along_joint_limit) =
      @equilibriumBadProbability_and_threshold_tendsto_zero_along_joint_limit := rfl


/-- Kernel-lock the strict probability-controlled persistent-window Tc. -/
theorem problem_strict_probabilistic_window_thermalization_time :
    (@microscopicWindowThermalizationTime) =
      @microscopicWindowThermalizationTime := rfl

/-- Kernel-lock monotonicity in the demanded persistence duration. -/
theorem problem_window_thermalization_time_monotone_duration :
    (@microscopicWindowThermalizationTime_monotone_duration) =
      @microscopicWindowThermalizationTime_monotone_duration := rfl

/-- Kernel-lock the fixed-volume obstruction: if every prospective start has
too much later failure probability, the strict Tc is infinite. -/
theorem problem_window_thermalization_time_top_of_every_start_fails :
    (@microscopicWindowThermalizationTime_eq_top_of_every_start_fails) =
      @microscopicWindowThermalizationTime_eq_top_of_every_start_fails := rfl

#print axioms problem_fixed_window_microscopic_kinetic_transfer
#print axioms problem_exists_sizeCutoff_for_equilibrium_expanding_windows
#print axioms problem_expanding_window_microscopic_kinetic_transfer
#print axioms problem_first_hit_le_persistent_equipartition_time
#print axioms problem_first_hit_eq_persistent_of_first_hit_persists
#print axioms problem_joint_strict_thermodynamic_persistence
#print axioms ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence.microscopicWindowThermalizationTime_monotone_duration
#print axioms ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence.microscopicWindowThermalizationTime_eq_top_of_every_start_fails
#print axioms ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence.equilibriumBadProbability_and_threshold_tendsto_zero_along_joint_limit

end ArchonPhysicsConsumers.Thermalization.ArbitrarilyLongMicroscopicKineticPersistence

import ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2

/-!
# Consumer: concrete canonical on-shell Rayleigh--Jeans F2 window
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.CanonicalOnShellRayleighJeansDistanceF2

set_option linter.hashCommand false in
#check @continuous_rayleighJeansDistance

set_option linter.hashCommand false in
#check @rayleighJeansDistance_nonnegative

set_option linter.hashCommand false in
#check @rayleighJeansDistance_eq_zero_of_equilibrium

set_option linter.hashCommand false in
#check @tendsto_rayleighJeansDistance_zero_of_canonicalOnShell

set_option linter.hashCommand false in
#check @exists_robustRayleighJeansHittingWindow_of_canonicalOnShell

set_option linter.hashCommand false in
#print axioms continuous_rayleighJeansDistance

set_option linter.hashCommand false in
#print axioms rayleighJeansDistance_nonnegative

set_option linter.hashCommand false in
#print axioms rayleighJeansDistance_eq_zero_of_equilibrium

set_option linter.hashCommand false in
#print axioms tendsto_rayleighJeansDistance_zero_of_canonicalOnShell

set_option linter.hashCommand false in
#print axioms exists_robustRayleighJeansHittingWindow_of_canonicalOnShell

end ArchonPhysicsConsumers.Thermalization

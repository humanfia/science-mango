import M7FactorReplay

def Frozen_pool_complete : Prop :=
 ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n

def Frozen_irreducible_check_exact : Prop :=
 ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p

def Frozen_factor_check_exact : Prop :=
 ∀ (F : M7.FactorReplay.BP) (factors : List (M7.FactorReplay.BP × ℕ)), M7.FactorReplay.check F factors = true ↔ (factors.map Prod.fst).Nodup ∧ (∀ t ∈ factors, t.1.Monic ∧ Irreducible t.1 ∧ 0 < t.2) ∧ M7.FactorReplay.product factors = F

def Frozen_self_check : Prop :=
 ∀ F : M7.FactorReplay.BP, F.Monic → M7.FactorReplay.check F (M7.FactorReplay.expected F) = true

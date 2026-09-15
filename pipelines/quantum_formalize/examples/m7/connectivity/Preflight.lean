import M7Connectivity

def Frozen_difference_shift : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A

def Frozen_difference_affine : Prop :=
  ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M7.Connectivity.differences (A.image (M7.Action.affine u s)) = (fun x : ZMod N => (u : ZMod N)*x) '' M7.Connectivity.differences A

def Frozen_closure_equiv_top : Prop :=
  ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤

def Frozen_connected_action : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Connectivity.Recipe N), M7.Connectivity.connected (M7.Action.act g c) ↔ M7.Connectivity.connected c

def Frozen_connected_shift : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N) (s t : ZMod N), M7.Connectivity.connected (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) ↔ M7.Connectivity.connected c

def Frozen_scalar_mem : Prop :=
  ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r*a ∈ H

def Frozen_one_mem_top : Prop :=
  ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)), (1 : ZMod N) ∈ H ↔ H = ⊤

def Frozen_gcd_mem : Prop :=
  ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H

def Frozen_finite_generation_gcd : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1

def Frozen_anchored_closure : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → AddSubgroup.closure (M7.Connectivity.differences A ∪ M7.Connectivity.differences B) = AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))

def Frozen_nat_support_image : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (fun a : ℕ => (a : ZMod N)) '' ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B : Finset ℕ) : Set ℕ) = (A : Set (ZMod N)) ∪ (B : Set (ZMod N))

def Frozen_anchored_gcd : Prop :=
  ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → (M7.Connectivity.connected (A,B) ↔ M7.Domain.connectivityGcd A B = 1)

def Frozen_connected_admissible : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M6.Final.Admissible N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)

def Frozen_anchor_admissible : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N), 0 < w → c.1.card = w → c.2.card = w → M7.Connectivity.connected c → ∃ q ∈ c.1, ∃ r ∈ c.2, M6.Final.Admissible N (M7.Supports.polynomial (M7.Domain.shift c.1 (-q))) (M7.Supports.polynomial (M7.Domain.shift c.2 (-r)))


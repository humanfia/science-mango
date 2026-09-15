import M7CompactStorage

def Frozen_support_value_injective : Prop :=
 ∀ (N : ℕ) [NeZero N], Function.Injective (@M7.CompactStorage.supportBits N) ∧ Function.Injective (@M7.CompactStorage.valueBits N)

def Frozen_polynomial_injective : Prop :=
 ∀ (N : ℕ) (F G : M5.BinaryPolynomial), F.natDegree ≤ N → G.natDegree ≤ N → M7.CompactStorage.polynomialBits N F = M7.CompactStorage.polynomialBits N G → F = G

def Frozen_field_bounds : Prop :=
 ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M7.RecipeSignature.signature c).natDegree ≤ N ∧ M7.ActualOrbit.stabilizerCount c < 2^(1+3*N)

def Frozen_emission_valid : Prop :=
 ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.CompactStorage.Valid (M7.CompactGeneration.emission w E bases)

def Frozen_encode_core : Prop :=
 ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), M7.CompactStorage.Valid e → M7.CompactStorage.Valid f → M7.CompactStorage.encode e = M7.CompactStorage.encode f → M7.CompactStorage.coreView e = M7.CompactStorage.coreView f

def Frozen_unit_table_recovery : Prop :=
 ∀ (N : ℕ) [NeZero N] (e : M7.CompactGeneration.Emission N) (u : (ZMod N)ˣ) (F : M5.BinaryPolynomial), F.natDegree ≤ N → (M7.CompactStorage.unitTable e u = M7.CompactStorage.polynomialBits N F ↔ M7.RecipeSignature.signature (M7.Action.act (⟨u,false,0,0⟩ : M7.Action.Record N) e.representative) = F)

def Frozen_storage_bounds : Prop :=
 ∀ (N H : ℕ) [NeZero N], M7.CompactStorage.coreBits N = 12*N+4 ∧ M7.CompactStorage.coreBits N ≤ 16*N ∧ M7.CompactStorage.tableBits N = Nat.totient N*(N+1) ∧ M7.CompactStorage.storedCoreBits N H ≤ 16*H*N ∧ M7.CompactStorage.storedWithTablesBits N H ≤ 16*H*N + 2*H*Nat.totient N*N

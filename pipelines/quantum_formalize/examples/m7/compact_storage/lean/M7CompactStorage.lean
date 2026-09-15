import M7CompactGenerationAccepted

namespace M7.CompactStorage
noncomputable section
open Classical
abbrev Bits (n : ℕ) := Fin n → Bool
noncomputable def supportBits {N : ℕ} (A : Finset (ZMod N)) : Bits N :=
  fun i => decide ((i.val : ZMod N) ∈ A)
noncomputable def valueBits {N : ℕ} (x : ZMod N) : Bits N :=
  fun i => decide ((i.val : ZMod N) = x)
noncomputable def polynomialBits (N : ℕ) (F : M5.BinaryPolynomial) : Bits (N+1) :=
  fun i => decide (F.coeff i.val = 1)
structure Code (N : ℕ) where
  leafLeft : Bits N
  leafRight : Bits N
  representativeLeft : Bits N
  representativeRight : Bits N
  unit : Bits N
  exchange : Bool
  leftShift : Bits N
  rightShift : Bits N
  leafSignature : Bits (N+1)
  representativeSignature : Bits (N+1)
  stabilizer : BitVec (1+3*N)
noncomputable def encode {N : ℕ} [NeZero N] (e : M7.CompactGeneration.Emission N) : Code N :=
  ⟨supportBits e.leaf.1, supportBits e.leaf.2,
   supportBits e.representative.1, supportBits e.representative.2,
   valueBits (e.action.unit : ZMod N), e.action.exchange,
   valueBits e.action.leftShift, valueBits e.action.rightShift,
   polynomialBits N e.leafSignature, polynomialBits N e.representativeSignature,
   BitVec.ofNat (1+3*N) e.stabilizer⟩
/-- The optional full prefix transcript is deliberately not part of the compact core. -/
def coreView {N : ℕ} [NeZero N] (e : M7.CompactGeneration.Emission N) :=
  (e.leaf,e.representative,e.action,e.leafSignature,e.representativeSignature,e.stabilizer)
def Valid {N : ℕ} [NeZero N] (e : M7.CompactGeneration.Emission N) : Prop :=
  M7.Action.act e.action e.leaf = e.representative ∧
  e.leafSignature = M7.RecipeSignature.signature e.leaf ∧
  e.representativeSignature = M7.RecipeSignature.signature e.representative ∧
  e.stabilizer = M7.ActualOrbit.stabilizerCount e.representative
/-- Exact sum of the widths of the eleven fields in Code, not runtime object bytes. -/
def coreBits (N : ℕ) : ℕ := 4*N + 3*N + 1 + 2*(N+1) + (1+3*N)
noncomputable def unitTable {N : ℕ} [NeZero N] (e : M7.CompactGeneration.Emission N)
    (u : (ZMod N)ˣ) : Bits (N+1) :=
  polynomialBits N (M7.RecipeSignature.signature
    (M7.Action.act (⟨u,false,0,0⟩ : M7.Action.Record N) e.representative))
noncomputable def tableBits (N : ℕ) [NeZero N] : ℕ := Fintype.card ((ZMod N)ˣ) * (N+1)
def storedCoreBits (N H : ℕ) : ℕ := H * coreBits N
noncomputable def storedWithTablesBits (N H : ℕ) [NeZero N] : ℕ :=
  storedCoreBits N H + H * tableBits N
end
end M7.CompactStorage

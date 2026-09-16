import Mathlib

namespace M7.Action
structure Record (N : ℕ) [NeZero N] where
  unit : (ZMod N)ˣ
  exchange : Bool
  leftShift : ZMod N
  rightShift : ZMod N
  deriving DecidableEq, Fintype

def identity (N : ℕ) [NeZero N] : Record N := ⟨1, false, 0, 0⟩
def compose {N : ℕ} [NeZero N] (g h : Record N) : Record N :=
  ⟨g.unit*h.unit, Bool.xor g.exchange h.exchange,
   (g.unit : ZMod N)*(if g.exchange then h.rightShift else h.leftShift)+g.leftShift,
   (g.unit : ZMod N)*(if g.exchange then h.leftShift else h.rightShift)+g.rightShift⟩
def inverse {N : ℕ} [NeZero N] (g : Record N) : Record N :=
  ⟨g.unit⁻¹, g.exchange,
   -((↑(g.unit⁻¹) : ZMod N)*(if g.exchange then g.rightShift else g.leftShift)),
   -((↑(g.unit⁻¹) : ZMod N)*(if g.exchange then g.leftShift else g.rightShift))⟩
def affine {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (s i : ZMod N) : ZMod N := u*i+s
abbrev Recipe (N : ℕ) := Finset (ZMod N) × Finset (ZMod N)
noncomputable def act {N : ℕ} [NeZero N] (g : Record N) (c : Recipe N) : Recipe N :=
  ((if g.exchange then c.2 else c.1).image (affine g.unit g.leftShift),
   (if g.exchange then c.1 else c.2).image (affine g.unit g.rightShift))
def translate {N : ℕ} [NeZero N] (s t : ZMod N) : Record N := ⟨1,false,s,t⟩
def multiplier {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) : Record N := ⟨u,false,0,0⟩
def exchange (N : ℕ) [NeZero N] : Record N := ⟨1,true,0,0⟩
end M7.Action

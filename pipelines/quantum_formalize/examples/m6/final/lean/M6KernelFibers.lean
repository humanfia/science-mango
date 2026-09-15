import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
namespace M6.KernelFibers
abbrev BP := Polynomial (ZMod 2)
noncomputable def embed (F K : BP) (hF : F.Monic) (z : AdjoinRoot F) : AdjoinRoot (F*K) :=
  AdjoinRoot.mk (F*K) (K * AdjoinRoot.modByMonicHom hF z)
def annihilator (F K : BP) := {z : AdjoinRoot (F*K) // AdjoinRoot.mk (F*K) F * z = 0}
end M6.KernelFibers

import M6CyclicAccepted
import M6KernelFibersAccepted
namespace M6.BoundaryFibers
abbrev BP := M6.Cyclic.BinaryPolynomial
noncomputable def boundary (a b M : BP) (h : AdjoinRoot M) : AdjoinRoot M × AdjoinRoot M :=
  (AdjoinRoot.mk M a * h, AdjoinRoot.mk M b * h)
end M6.BoundaryFibers

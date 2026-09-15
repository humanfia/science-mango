import M6ActualTransfer
import M6QueryResourcesAccepted
import M6EuclidStorage
namespace M6.ActualTransfer
noncomputable def actualSolveStorage (N : ℕ) (a b : BP) : ℕ :=
  M6.Transfer.solveStorage (span a b) N (M6.EuclidStorage.actualPreprocessStorage N)
end M6.ActualTransfer

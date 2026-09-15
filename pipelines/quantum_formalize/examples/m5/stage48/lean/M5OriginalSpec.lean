import M5ArithmeticWorkflowAccepted
import M5PeriodSearchAccepted
import M5TranslationAccepted
import M5PhysicalRecovery
import M5ArithmeticResidueRecovery

namespace M5.Final

def PeriodClause (F : M5.BinaryPolynomial) : Prop :=
  0 < M5.signaturePeriod F ∧ M5.PeriodSearch.finiteSearch F = M5.signaturePeriod F ∧ (∀ N : ℕ, F ∣ M5.cyclicModulus N ↔ M5.signaturePeriod F ∣ N) ∧ M5.PeriodSearch.finiteSearch (1 : M5.BinaryPolynomial) = 1

def OrderClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  ∀ N : ℕ, 0 < N → 0 ≤ M5.OrderCount.C N w F ∧ (0 < M5.OrderCount.C N w F ↔ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)) ∧ (M5.OrderCount.C N w F = 0 ↔ ¬ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U)) ∧ (F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card)

def LowerClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  ∀ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U → M5.signaturePeriod F ∣ N ∧ max w (F.natDegree + 1) ≤ N

def WeightOneClause (F : M5.BinaryPolynomial) : Prop :=
  ∀ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N 1 F S U ↔ N = 1 ∧ F = 1 ∧ S = {0} ∧ U = {0}

def GlobalClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  0 ≤ M5.ResidueCount.A w F ∧ (0 < M5.ResidueCount.A w F ↔ ∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U) ∧ (M5.ResidueCount.A w F = 0 ↔ ¬ (∃ (N : ℕ) (S U : Finset ℕ), M5.PhysicalOrder.realizes N w F S U))

def ProgressionClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  0 < M5.ResidueCount.A w F → ∃ (S U : Finset ℕ) (N E : ℕ), 0 < E ∧ N < M5.birthBound w (M5.signaturePeriod F) ∧ ∀ j : ℕ, M5.PhysicalOrder.realizes (N + j * E) w F S U

def BirthClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  (0 < M5.ResidueCount.A w F → ∃ b : ℕ, M5.ArithmeticWorkflow.birth w F = some b ∧ b ≤ M5.birthBound w (M5.signaturePeriod F) ∧ max w (F.natDegree + 1) ≤ b ∧ M5.signaturePeriod F ∣ b ∧ 0 < M5.OrderCount.C b w F ∧ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes b w F S U) ∧ ∀ N : ℕ, (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U) → b ≤ N) ∧ (M5.ArithmeticWorkflow.birth w F = none ↔ M5.ResidueCount.A w F = 0)

def LaterClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  ∀ b N : ℕ, M5.ArithmeticWorkflow.birth w F = some b → b ≤ N → ((¬ M5.signaturePeriod F ∣ N ∨ M5.OrderCount.C N w F = 0) ↔ ¬ (∃ S U : Finset ℕ, M5.PhysicalOrder.realizes N w F S U))

def OrderRecoveryClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  ∀ N : ℕ, 0 < N → 0 < M5.OrderCount.C N w F → (M5.PhysicalRecovery.recoverWord N w F).length = 2 * (N-1) ∧ M5.PhysicalOrder.realizes N w F (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.recoverWord N w F)) (M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.recoverWord N w F))

def ResidueRecoveryClause (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  0 < M5.ResidueCount.A w F → ∃ u : List (Fin (M5.signaturePeriod F)), (M5.ArithmeticResidueRecovery.recover w F).1 = some u ∧ u.length = 2 * (w-1) ∧ M5.ArithmeticResidueRecovery.wordValid w F u ∧ (M5.ArithmeticResidueRecovery.recover w F).2 ≤ 2 * (w-1) * (M5.signaturePeriod F)

def NormalizationClause : Prop :=
  ∀ (N : ℕ) [NeZero N] (S U : Finset (ZMod N)), S.Nonempty → U.Nonempty → ∃ A B : Finset ℕ, A.card = S.card ∧ B.card = U.card ∧ 0 ∈ A ∧ 0 ∈ B ∧ (∀ a ∈ A, a < N) ∧ (∀ b ∈ B, b < N) ∧ M5.Connectivity.supportGcd N A B = M5.Translation.differenceGcd S U ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = M5.completeSignature (M5.Translation.supportPolynomial S) (M5.Translation.supportPolynomial U) N

def OriginalM5Core (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  PeriodClause F ∧ OrderClause w F ∧ LowerClause w F ∧ WeightOneClause F ∧
  NormalizationClause ∧
  (2 ≤ w → GlobalClause w F ∧ ProgressionClause w F ∧ BirthClause w F ∧ LaterClause w F)

def OriginalM5Spec (w : ℕ) (F : M5.BinaryPolynomial) : Prop :=
  OriginalM5Core w F ∧ OrderRecoveryClause w F ∧
  (2 ≤ w → ResidueRecoveryClause w F)

end M5.Final

import M5OrderCount
import M5GlobalCriterionReady
import M5OrderBoundaryAccepted
import M5BirthSearchAccepted

namespace M5.ArithmeticWorkflow
noncomputable def birth (w : ℕ) (F : M5.BinaryPolynomial) : Option ℕ :=
  M5.BirthSearch.birth (M5.signaturePeriod F) (max w (F.natDegree + 1))
    (M5.birthBound w (M5.signaturePeriod F)) (fun N => M5.OrderCount.C N w F)
end M5.ArithmeticWorkflow

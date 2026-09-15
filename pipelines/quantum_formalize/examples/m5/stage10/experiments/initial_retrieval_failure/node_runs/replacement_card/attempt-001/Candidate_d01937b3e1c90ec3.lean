import FrozenTarget_d01937b3e1c90ec3
theorem M5.RepairSupport.replacement_card : QuantumHarnessFrozenTarget := by
  intro A e q he hq
  change (insert q (A.erase e)).card = A.card
  have hq' : q ∉ A.erase e := fun h => hq (Finset.mem_of_mem_erase h)
  calc
    (insert q (A.erase e)).card = (A.erase e).card + 1 :=
      Finset.card_insert_of_notMem hq'
    _ = (insert e (A.erase e)).card :=
      (Finset.card_insert_of_notMem (Finset.not_mem_erase e A)).symm
    _ = A.card := congrArg Finset.card (Finset.insert_erase he)

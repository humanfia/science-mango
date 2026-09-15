import FrozenTarget_24edb672cc3528d2
theorem M7.Factorized.exact_target_card : QuantumHarnessFrozenTarget := by
  intro U S T instU instS instT X Y leftImage rightImage x y
  classical
  simpa [M7.Factorized.exactTargetNumerator, M7.Factorized.records, M7.Factorized.count] using
    (M7.Factorized.numerator_record_card U S T (fun _ => True)
      (fun u s => leftImage u s = x) (fun u t => rightImage u t = y))

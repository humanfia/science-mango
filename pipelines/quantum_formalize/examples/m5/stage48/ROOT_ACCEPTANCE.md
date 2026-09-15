# Exact root acceptance

The final declaration is fixed as:

```lean
M5.Final.original_m5 :
  ∀ (w : ℕ) (F : M5.BinaryPolynomial),
    0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F
```

`OriginalM5Spec` expands through the committed M5OriginalSpec definition file, with actual A/C/birth/recovery functions. The source contract mapping is in ../final_scope. It is not enough to accept a theorem bearing this name against an altered weaker definition.

The final audit should:

1. Verify the fixed root type and the frozen primary definition hashes.
2. Confirm46/47 gates have been resolved by actual accepted imports and no pending theorem/axiom adapter is being used as a proof.
3. Verify the accepted root node payload, exact target/candidate correspondence and source hashes; keep all component provenance and accepted imported proofs.
4. Compile a final root module importing the exact accepted closure. In a separate module, check an example with the exact public type assigned to M5.Final.original_m5 and print its axioms.
5. Require successful combined compile, exact-type import, source/environment stability and only propext/Classical.choice/Quot.sound in root axioms.
6. Record the original-clause correspondence and zero remaining original obligations. Preserve individual component successes and failed attempts regardless of the final root outcome.

A dedicated ROOT_ACCEPTANCE.json should then record the source/spec/root hashes, accepted closure references, independent exact-type import, actual root axioms, and `original_m5_formalized=true` only on success. It must not copy a success template before these checks have occurred.

The component scheduler emits `m5_formalized=false` as a constant. Do not change historical receipts and do not interpret this field as a semantic rejection of a completed root. The dedicated root result answers the final completion question. Once the exact original contract passes, no new stronger completion gate is introduced.

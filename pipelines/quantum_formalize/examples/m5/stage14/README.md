# Stage 14: fixed-cardinality subset character counting

This experiment translates the subset-generating-polynomial identity in reviewed M5 section 2. For each finite available-position set S, the polynomial is the product of 1+C(character(f(s)))*X. Its powerset expansion keeps the full vector sum for each subset, including characteristic-two cancellations. Taking coefficient k restricts precisely to S.powersetCard k; orthogonality then gives 2^D times the number of such subsets with vector sum z.

The five targets are a local zero-character helper, character of finite vector sum, generating polynomial expansion, fixed-cardinality coefficient, and the final integer counting identity. All allow S empty, k=0, D=0 and k>|S|. No positivity premise is added to avoid these boundary cases.

The powerset appears as a symbolic proof identity, not as the claimed evaluation algorithm. Later integration must connect this coefficient to the closed signed-binomial expression from stage11 and transport vector coordinates to the polynomial quotient. Neither task is declared completed by this experiment, and no raw support-pair evaluation is introduced.

The signedProduct body is byte-identical to the stage11 expression, but has its own M5.SubsetCharacter namespace to avoid duplicate declarations. It imports no stage11 or stage15 result. The actual imported proof dependencies are immutable52 M5.Character.character_add and character_orthogonality; its BinaryVector/value definitions are unchanged. All source modules were copied verbatim with hashes in IMPORT_PROVENANCE.json, and rebuilt independently.

Project: /home/jing/m5-lean-subset-character-formalization. Graph contexts are empty; GraphPreflight.lean is generated from decoded graph imports and exact statement strings. Runtime load_graph and typechecks are recorded separately from proof acceptance. No new proofs or models are run during preparation.

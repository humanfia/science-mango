# Compact record logical bit encoding

The actual Emission contains both leaf and representative, so all four support masks are counted. Code uses four N-bit masks, three N-bit one-hot residues plus exchange, two (N+1)-bit complete polynomial coefficient vectors, and a (1+3N)-bit actual stabilizer. Its layout is 12N+4≤16N bits. Valid is only actual field consistency; emission_valid discharges it for the literal generation constructor. encode_core recovers every field of coreView, deliberately excluding path.

The optional complete List DescentTrace.Step path stores prefixes and integer residual evidence; it is NOT included or claimed to fit the core HN bound. A separate optional per-unit full-signature table has totient(N)*(N+1) bits per record, giving a further≤2H*totient(N)*N bits. These are finite logical encodings, not host Lean object sizes, serializer correctness or compiler/runtime claims.

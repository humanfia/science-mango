# Exact finite birth search

The executable search forms the finite set of orders up to B meeting lower/period constraints and having positive arithmetic count, then returns its minimum or none. It never scans support pairs.

The generic correctness theorem takes necessary order bounds, exact count correctness on candidate orders, and a bounded valid witness. Final M5 must instantiate these using the accepted lower-order results, exact C, and the source construction from A; this component does not add a physical-witness premise to M5. The none theorem alone only certifies the finite search interval. Global absence requires the completed global criterion.

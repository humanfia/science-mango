# Actual recurrence coefficient bounds accepted

All eight targets passed normal frozen acceptance, combined assembly and unchanged-environment checks. The actual signed polynomial recurrence satisfies rowMass(layers at n)<=8^n for edge mass<=4 and trace coefficient absolute value<=2^R*8^N. Edge degree<=2 gives actual layer degree<=2*n, including zero/cancellation cases. These are verified proof imports, not abstract efficiency assumptions.

Actual scalar scatter equivalence and intermediate event-prefix bounds are the remaining resource links; final-array magnitude alone is not used to certify arbitrary partial sums.

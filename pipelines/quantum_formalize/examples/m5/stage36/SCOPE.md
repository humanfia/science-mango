# Binary branch recovery

recover evaluates the exclusion-child count and appends false if it is positive, otherwise true, then recurses on one fewer undecided position. It is a structurally terminating Lean function and does not enumerate support pairs.

Theorems establish the exact number of appended binary decisions, positivity preservation under the completion-count partition identity, and terminal validity. These generic input hypotheses are not substitutes for M5's arithmetic completion theorem: the full recipe recovery must instantiate the count by the explicit divisor/character completion formula and prove its partition and terminal properties. Taking m=2(N-1) then matches the source physical-position decision bound.

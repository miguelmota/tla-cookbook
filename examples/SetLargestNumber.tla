---- MODULE SetLargestNumber ----

EXTENDS Integers, TLC

\* Returns the largest element of finite set S of integers,
\* or -1 if S is the empty set.
Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S: y <= x

Init == TRUE
Next ==
  /\ Print(<<Maximum({4,7,5})>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

---- MODULE SetSmallestNumber ----

EXTENDS Integers, TLC

\* Returns the smallest element of finite set S of integers,
\* or -1 if S is the empty set.
Minimum(S) == IF S = {} THEN -1 ELSE CHOOSE x \in S: \A y \in S \ {x}: y > x

Init == TRUE
Next ==
  /\ Print(<<Minimum({4,7,5})>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

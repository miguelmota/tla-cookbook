---- MODULE SetCommon ----

EXTENDS TLC
CONSTANT S, T

Init ==
  /\ S = {1, 2, 3}
  /\ T = {{1,2}, {1,3}, {2,3}}

Next ==
  \* asserts that any two elements of T have an element in common
  /\ \A X, Y \in T : X \cap Y # {}
  /\ UNCHANGED <<S, T>>

ASSUME
  /\ T \subseteq SUBSET S

Spec == Init /\ [][Next]_<<S, T>>
====

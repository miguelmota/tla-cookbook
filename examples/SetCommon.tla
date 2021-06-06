---- MODULE SetCommon ----

EXTENDS TLC
CONSTANT S, T, R

Init ==
  /\ S = {1, 2, 3}
  /\ T = {{1, 2}, {1, 3}, {2, 3}}
  /\ R = {{1, 2}, {1, 3}, {2, 3}}

Next ==
  \* asserts that any two elements of T have an element in common
  /\ Print(<<\A X, Y \in T : X \cap Y # {}>>, TRUE)
  /\ Print(<<\A X, Y \in R : X \cap Y # {}>>, TRUE)

ASSUME
  /\ T \subseteq SUBSET S

Spec == Init /\ [][Next]_<<S, T, R>>
====

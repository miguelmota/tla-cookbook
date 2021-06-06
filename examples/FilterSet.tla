---- MODULE FilterSet ----

EXTENDS Integers, TLC
VARIABLE S

Init ==
  /\ S = {1, 2, 3, 4, 5}

Next ==
  /\ Print(<<{v \in S : v > 3}>>, TRUE)
  /\ UNCHANGED <<S>>

Spec == Init /\ [][Next]_<<S>>
====

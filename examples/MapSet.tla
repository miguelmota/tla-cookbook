---- MODULE MapSet ----

EXTENDS Integers, TLC
VARIABLE S

Init ==
  /\ S = {1, 2, 3, 4, 5}

Next ==
  /\ Print(<<{v^2: v \in S}>>, TRUE)
  /\ UNCHANGED <<S>>

Spec == Init /\ [][Next]_<<S>>
====

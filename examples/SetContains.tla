---- MODULE SetContains ----

EXTENDS Integers, TLC

Init == TRUE
Next ==
  /\ Print(<<2 \in {1, 2, 3}>>, TRUE)
  /\ Print(<<4 \in 1..3>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

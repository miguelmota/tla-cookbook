---- MODULE RangeSet ----

EXTENDS Integers, TLC

Init == TRUE
Next ==
  /\ Print(<<1..5>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

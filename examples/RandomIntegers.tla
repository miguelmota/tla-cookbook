---- MODULE RandomIntegers ----

EXTENDS Integers, TLC

Init == TRUE
Next ==
  /\ Print(<<RandomElement(1..100)>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

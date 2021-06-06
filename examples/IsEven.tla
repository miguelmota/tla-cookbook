---- MODULE IsEven ----

EXTENDS Integers, TLC

IsEven(x) == x % 2 = 0

Init == TRUE
Next ==
  /\ Print(<<IsEven(2)>>, TRUE)
  /\ Print(<<IsEven(3)>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

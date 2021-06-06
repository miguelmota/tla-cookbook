---- MODULE IsOdd ----

EXTENDS Integers, TLC

IsOdd(x) == x % 2 = 1

Init == TRUE
Next ==
  /\ Print(<<IsOdd(2)>>, TRUE)
  /\ Print(<<IsOdd(3)>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

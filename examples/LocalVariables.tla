---- MODULE LocalVariables ----

EXTENDS Integers, TLC

Init == TRUE
Next ==
  /\ LET x == 1
         y == 2
         z == 3
     IN Print(<<x + y + z>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

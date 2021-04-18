---- MODULE SetDifference ----

EXTENDS Integers, TLC
VARIABLE S, T

Init ==
  /\ S = (10..20)
  /\ T = (1..14)

Next ==
  \* S \ T is the set of elements in S not in T
  /\ Print(<<S \ T>>, TRUE)
  /\ UNCHANGED <<S, T>>

Spec == Init /\ [][Next]_<<S, T>>
====

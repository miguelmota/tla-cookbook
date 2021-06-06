---- MODULE Print ----

EXTENDS TLC

Init == TRUE
Next ==
  /\ Print(<<"Hello world">>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

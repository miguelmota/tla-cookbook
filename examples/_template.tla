---- MODULE _template ----

EXTENDS TLC

Init == TRUE
Next ==
  /\ TRUE

Spec == Init /\ [][Next]_<<>>
====

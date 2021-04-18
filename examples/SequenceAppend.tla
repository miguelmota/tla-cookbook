---- MODULE SequenceAppend ----

EXTENDS Sequences, TLC
VARIABLE S

Init ==
  /\ S = <<1>>
Next ==
  /\ S' = S \o <<2>>
  /\ Print(<<S'>>, FALSE)

Spec == Init /\ [][Next]_<<S>>
====

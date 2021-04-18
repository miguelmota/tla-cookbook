---- MODULE SumSequence ----

EXTENDS Integers, Sequences, TLC

SumSeq(S) ==
  LET seq == S
    Sum[i \in 1..Len(seq)] == IF i = 1 THEN seq[i] ELSE seq[i] + Sum[i-1]
  IN IF seq = <<>> THEN 0 ELSE Sum[Len(seq)]

Init == TRUE
Next ==
  /\ Print(<<SumSeq(<<1, 2, 3>>)>>, TRUE)

Spec == Init /\ [][Next]_<<>>
====

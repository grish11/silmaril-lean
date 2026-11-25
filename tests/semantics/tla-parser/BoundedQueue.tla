---- MODULE BoundedQueue ----
EXTENDS Naturals, Sequences
CONSTANTS Messages, Capacity
VARIABLE q
ASSUME Capacity \in Nat

Init == q = <<>>
Enqueue(m) ==
  /\ Len(q) < Capacity
  /\ q' = Append(q, m)
Dequeue ==
  /\ q # <<>>
  /\ q' = Tail(q)
Next ==
  \/ \E m \in Messages : Enqueue(m)
  \/ Dequeue
TypeOK ==
  /\ q \in Seq(Messages)
  /\ Len(q) <= Capacity
Spec ==
  /\ Init
  /\ [][Next]_q
  /\ WF_q(Dequeue)
THEOREM QueueSafety == Spec => []TypeOK
<1>1. Init => TypeOK
  OBVIOUS
<1>2. TypeOK /\ [Next]_q => TypeOK'
  PROOF OMITTED
<1>3. QED BY <1>1, <1>2 DEF Spec
====

---- MODULE ProofSteps ----
THEOREM T == TRUE
PROOF
<003>prep.. DEFINE LOCAL F(x) == x
  G[y \in S] == F(y)
<*>plain H == INSTANCE M WITH C <- +
  -|- J == F(0)
<3> INSTANCE M WITH C <- <03>prep
<3>*.. HAVE <003>prep(1)!Label(2)!1
<3>-.. TAKE <<x,y>> \in S, z,w \in V
<3>... WITNESS <<x,y>> \in S, <*>prep!:
<*> PICK p,q : P(p,q)
  PROOF BY ONLY MODULE M, <*>prep DEF <3>prep, MODULE N
<3>case_label CASE C
  <+>.. SUFFICES ASSUME NEW k \in S PROVE P(k)
    PROOF
    <*> HAVE TRUE
    <5> QED PROOF OBVIOUS
  <4> QED
<3> USE ONLY <3>prep DEF H
<3> HIDE DEF G
<3>last ASSUME TRUE PROVE TRUE
  <9> QED PROOF OMITTED
<3>end QED
  <+> QED BY <*>unknown
THEOREM U == TRUE
<*> QED
====

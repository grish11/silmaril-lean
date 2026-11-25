---- MODULE Compatibility ----
ASSUME -|- Named ≜ TRUE

Overlay ==
  /\ [r EXCEPT !.v = @ @@ patch] = expected
  ∧ M!@@!1!@ = wanted
OverlayOrder == a@@b@@c := d
UsesOperator == F(×)
Tagged == a * Item(x):: (b + x)
Substitution == LET I == INSTANCE M WITH F <- + IN I

USE
---- MODULE Child ----
VARIABLE value
====

THEOREM TRUE
<1> QED BY
---- MODULE Sibling ----
====
====

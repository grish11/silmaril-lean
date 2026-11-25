---- MODULE Latch ----
VARIABLE flag

Init == flag = FALSE
Next == flag' = ~flag
====

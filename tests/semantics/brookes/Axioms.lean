module

import Silmaril.Semantics.Brookes.Thms

open Silmaril.Semantics.Brookes

#print axioms Transition
#print axioms Trace
#print axioms Rewrite
#print axioms Reduces
#print axioms Reduces.trans
#print axioms close
#print axioms Behavior
#print axioms Shuffle
#print axioms Runs
#print axioms Behavior.generate
#print axioms Behavior.atomic
#print axioms Behavior.ret
#print axioms Behavior.bind
#print axioms Behavior.forget
#print axioms Behavior.completes
#print axioms Command
#print axioms Command.skip
#print axioms Command.seq
#print axioms Command.parallel
#print axioms Reduces.append_left
#print axioms Reduces.append_right
#print axioms Reduces.append
#print axioms close_extensive
#print axioms close_mono
#print axioms close_stable
#print axioms close_least
#print axioms close_idem
#print axioms Runs.append_iff
#print axioms Runs.of_reduces
#print axioms Runs.reduces_singleton
#print axioms Behavior.ext
#print axioms Behavior.generate_accepts
#print axioms Behavior.generate_eq
#print axioms Behavior.completes_generate_iff
#print axioms Behavior.atomic_accepts_iff
#print axioms Behavior.atomic_completes_iff
#print axioms Behavior.ret_accepts_iff
#print axioms Behavior.bind_accepts_iff
#print axioms Behavior.ret_bind
#print axioms Behavior.bind_ret
#print axioms Behavior.bind_assoc
#print axioms Behavior.forget_bind_const
#print axioms Shuffle.comm
#print axioms Shuffle.append
#print axioms Shuffle.of_reduces_left
#print axioms Command.seq_assoc
#print axioms Command.skip_seq
#print axioms Command.seq_skip
#print axioms Command.seq_completes_iff
#print axioms Command.parallel_accepts_iff
#print axioms Command.parallel_generate
#print axioms Command.parallel_comm
#print axioms Command.seq_le_parallel
#print axioms Command.parallel_completes_iff
#print axioms Command.skip_parallel
#print axioms Command.parallel_skip

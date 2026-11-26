module

public import Silmaril.Semantics.Brookes.Defs
import Silmaril.Proofs.Semantics.Brookes.Closure
import Silmaril.Proofs.Semantics.Brookes.Bind
import Silmaril.Proofs.Semantics.Brookes.Parallel

public section

namespace Silmaril.Semantics.Brookes

universe u v w z

variable {Store : Type u} {A : Type v} {B : Type w} {C : Type z}

theorem Reduces.append_left {source target : Trace Store}
    (h : Reduces source target) (pre : Trace Store) : Reduces (pre ++ source) (pre ++ target) :=
  Proofs.Semantics.Brookes.reduces_append_left h pre

theorem Reduces.append_right {source target : Trace Store}
    (h : Reduces source target) (post : Trace Store) : Reduces (source ++ post) (target ++ post) :=
  Proofs.Semantics.Brookes.reduces_append_right h post

theorem Reduces.append {left left' right right' : Trace Store}
    (h₁ : Reduces left left') (h₂ : Reduces right right') :
    Reduces (left ++ right) (left' ++ right') :=
  Proofs.Semantics.Brookes.reduces_append h₁ h₂

theorem close_extensive {seed : Trace Store → A → Prop} {trace : Trace Store} {value : A}
    (h : seed trace value) : close seed trace value :=
  Proofs.Semantics.Brookes.close_extensive h

theorem close_mono {seed covering : Trace Store → A → Prop}
    (h : ∀ ⦃trace value⦄, seed trace value → covering trace value)
    {trace value} (mem : close seed trace value) : close covering trace value :=
  Proofs.Semantics.Brookes.close_mono h mem

theorem close_stable {seed : Trace Store → A → Prop} {source target : Trace Store} {value : A}
    (h : close seed source value) (step : Reduces source target) : close seed target value :=
  Proofs.Semantics.Brookes.close_stable h step

theorem close_least {seed covering : Trace Store → A → Prop}
    (includes : ∀ ⦃trace value⦄, seed trace value → covering trace value)
    (stable : ∀ ⦃source target value⦄, covering source value → Reduces source target →
      covering target value)
    {trace value} (mem : close seed trace value) : covering trace value :=
  Proofs.Semantics.Brookes.close_least includes stable mem

theorem close_idem (seed : Trace Store → A → Prop) : close (close seed) = close seed :=
  Proofs.Semantics.Brookes.close_idem seed

theorem Runs.append_iff {s t : Store} {left right : Trace Store} :
    Runs s (left ++ right) t ↔ ∃ m, Runs s left m ∧ Runs m right t :=
  Proofs.Semantics.Brookes.runs_append

/-- Deductions cannot remove a genuine store gap from a complete execution. -/
theorem Runs.of_reduces {s t : Store} {source target : Trace Store}
    (h : Reduces source target) (run : Runs s target t) : Runs s source t :=
  Proofs.Semantics.Brookes.runs_of_reduces h run

theorem Runs.reduces_singleton {s t : Store} {trace : Trace Store}
    (run : Runs s trace t) (hne : trace ≠ []) : Reduces trace [(s, t)] :=
  Proofs.Semantics.Brookes.reduces_singleton_of_runs run hne

namespace Behavior

theorem ext {first second : Behavior Store A}
    (accepts : ∀ trace value, first.accepts trace value ↔ second.accepts trace value) :
    first = second :=
  Proofs.Semantics.Brookes.behavior_ext accepts

theorem generate_accepts {seed : Trace Store → A → Prop} {trace : Trace Store} {value : A}
    (hne : trace ≠ []) (hs : seed trace value) : (generate seed).accepts trace value :=
  Proofs.Semantics.Brookes.generate_accepts hne hs

theorem generate_eq (behavior : Behavior Store A) : generate behavior.accepts = behavior :=
  Proofs.Semantics.Brookes.generate_eq behavior

/-- A singleton observation is equivalent to a contiguous execution of a nonempty seed. -/
theorem completes_generate_iff {seed : Trace Store → A → Prop} {s t : Store} {value : A} :
    (generate seed).completes s t value ↔
      ∃ trace, trace ≠ [] ∧ seed trace value ∧ Runs s trace t :=
  Proofs.Semantics.Brookes.completes_generate_iff

theorem atomic_accepts_iff {step : Store → Store → A → Prop} {trace : Trace Store} {value : A} :
    (atomic step).accepts trace value ↔ ∃ s t, step s t value ∧ Reduces [(s, t)] trace :=
  Proofs.Semantics.Brookes.atomic_accepts_iff

theorem atomic_completes_iff {step : Store → Store → A → Prop} {s t : Store} {value : A} :
    (atomic step).completes s t value ↔ step s t value :=
  Proofs.Semantics.Brookes.atomic_completes_iff

theorem ret_accepts_iff {value result : A} {trace : Trace Store} :
    (ret value).accepts trace result ↔ ∃ s, result = value ∧ Reduces [(s, s)] trace :=
  Proofs.Semantics.Brookes.ret_accepts_iff

theorem bind_accepts_iff {first : Behavior Store A} {next : A → Behavior Store B}
    {trace : Trace Store} {result : B} :
    (first.bind next).accepts trace result ↔
      ∃ left right value, first.accepts left value ∧ (next value).accepts right result ∧
        Reduces (left ++ right) trace :=
  Proofs.Semantics.Brookes.bind_accepts_iff

theorem ret_bind (value : A) (next : A → Behavior Store B) :
    (ret value).bind next = next value :=
  Proofs.Semantics.Brookes.ret_bind value next

theorem bind_ret (first : Behavior Store A) : first.bind ret = first :=
  Proofs.Semantics.Brookes.bind_ret first

theorem bind_assoc (first : Behavior Store A) (next : A → Behavior Store B)
    (last : B → Behavior Store C) :
    (first.bind next).bind last = first.bind (fun value => (next value).bind last) :=
  Proofs.Semantics.Brookes.bind_assoc first next last

theorem forget_bind_const (first : Behavior Store A) (second : Behavior Store B) :
    (first.bind (fun _ => second)).forget = Command.seq first.forget second.forget :=
  Proofs.Semantics.Brookes.forget_bind_const first second

end Behavior

namespace Shuffle

theorem comm {Step : Type u} {left right merged : List Step}
    (merge : Shuffle left right merged) : Shuffle right left merged :=
  Proofs.Semantics.Brookes.shuffle_comm merge

theorem append {Step : Type u} (left right : List Step) : Shuffle left right (left ++ right) :=
  Proofs.Semantics.Brookes.shuffle_append left right

/-- A deduction on the left input can be performed after interleaving instead. -/
theorem of_reduces_left {left left' right merged : Trace Store}
    (deduction : Reduces left left') (merge : Shuffle left' right merged) :
    ∃ raw, Shuffle left right raw ∧ Reduces raw merged :=
  Proofs.Semantics.Brookes.shuffle_of_reduces_left deduction merge

end Shuffle

namespace Command

theorem seq_assoc (first second third : Command Store) :
    seq (seq first second) third = seq first (seq second third) :=
  Behavior.bind_assoc first (fun _ => second) (fun _ => third)

theorem skip_seq (command : Command Store) : seq skip command = command :=
  Behavior.ret_bind () (fun _ => command)

theorem seq_skip (command : Command Store) : seq command skip = command :=
  Behavior.bind_ret command

/-- On initial/final-store observations, sequencing is relational composition. -/
theorem seq_completes_iff {first second : Command Store} {s t : Store} :
    (seq first second).completes s t () ↔
      ∃ middle, first.completes s middle () ∧ second.completes middle t () :=
  Proofs.Semantics.Brookes.seq_completes_iff

theorem parallel_accepts_iff {first second : Command Store} {trace : Trace Store} :
    (parallel first second).accepts trace () ↔
      ∃ left right merged, first.accepts left () ∧ second.accepts right () ∧
        Shuffle left right merged ∧ Reduces merged trace :=
  Proofs.Semantics.Brookes.parallel_accepts_iff

/-- Interleaving raw seeds and closing once gives the same behavior as closing
both operands before the interleaving. -/
theorem parallel_generate (leftSeed rightSeed : Trace Store → Unit → Prop) :
    parallel (Behavior.generate leftSeed) (Behavior.generate rightSeed) =
      Behavior.generate (fun word _ =>
        ∃ left right, left ≠ [] ∧ right ≠ [] ∧ leftSeed left () ∧ rightSeed right () ∧
          Shuffle left right word) :=
  Proofs.Semantics.Brookes.parallel_generate leftSeed rightSeed

theorem parallel_comm (first second : Command Store) :
    parallel first second = parallel second first :=
  Proofs.Semantics.Brookes.parallel_comm first second

theorem seq_le_parallel {first second : Command Store} {trace : Trace Store}
    (h : (seq first second).accepts trace ()) : (parallel first second).accepts trace () :=
  Proofs.Semantics.Brookes.seq_le_parallel h

/-- A closed initial/final-store observation is witnessed by a finite schedule
whose merged word runs on one store from start to finish. -/
theorem parallel_completes_iff {first second : Command Store} {s t : Store} :
    (parallel first second).completes s t () ↔
      ∃ left right merged, first.accepts left () ∧ second.accepts right () ∧
        Shuffle left right merged ∧ Runs s merged t :=
  Proofs.Semantics.Brookes.parallel_completes_iff

theorem skip_parallel (command : Command Store) : parallel skip command = command :=
  Proofs.Semantics.Brookes.parallel_skip_left command

theorem parallel_skip (command : Command Store) : parallel command skip = command :=
  (parallel_comm command skip).trans (skip_parallel command)

end Command
end Silmaril.Semantics.Brookes

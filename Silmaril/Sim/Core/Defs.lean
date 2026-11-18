module

public import Silmaril.Prelude.Defs
public import Silmaril.Machine.Execution

/-!
# Simulators: partial states, machines, programs, soundness (header)

The ISA-agnostic core of the region `Sim` (guide:
`docs/projects/wasm-sim.md`). A *simulator* (a Wasm module, in the end) and a *reference machine* (an
ISA semantics) are both `Machine`s: a hidden state, a partial **view** of named locations, and
a labelled step relation. Soundness is a simulation of the simulator by the reference that
loses no information on the view; properties of programs then transfer (`Thms`).

* `PState L V := L → Option V`: a partial state; `none` is "unmodelled or undefined".
  `PState.Le` (`p ⊑ q`, the information order), `join`, `meet`, `comap` (restriction along a
  map of locations), `override` (frame: new values on a set, old ones elsewhere), `pushAlong`
  (write back along an embedding of locations).
* `Prog C L V`: programs over commands `C` (instruction forms, syscalls, simulator methods):
  `skip`, `cmd`, `test` (a guard on the view), `seq`, `choice`, `star`, `pick` (choice of a
  value). `subst` is
  substitution of programs for commands (and of locations), the *derived signature morphisms*
  of the institution (`Silmaril.Sim.Institution`): inlining callees, compiling an instruction to
  simulator calls. `MonoTests`: every guard is upward closed in `⊑`.
* `Machine C L V`: `St`, `view : St → PState L V`, `step : C → St → St → Prop`;
  `Machine.Sem M p`: the relational semantics of a program; `Machine.reduct`: a machine seen
  through a substitution (fewer commands, fewer locations).
* Properties: `Angelic M P p Q` (from every `P`-state, *some* run of `p` ends `Q`-related:
  the shape of `FnContract.Spec.Total`), `Demonic M P p Q` (every run does: partial
  correctness, the shape of `Silmaril.Wasm.Verify.Verified`/`FSpecValid`), `Progress M P p`
  (some run exists). The `H…` forms speak of hidden states, the plain ones of views.
* `Simulation A B` (**soundness** of the simulator `A` w.r.t. the reference `B`): a relation
  `R` with `A.view a ⊑ B.view b`, every `A`-step matched by a `B`-step with the same command,
  and **loading**: every `B`-state is related to an `A`-state with the same view.
  `CoSimulation A B` (**completeness**: every `B`-step is matched by an `A`-step, views equal),
  `Equiv A B` (both, views equal: the G ≡ M representation equivalence).
* Partial-state simulators (`PRel`, `PSim`): a simulator whose state *is* its view.
  `PRel.Sound`, the refinement order `PRel.Le`, `bot`, `havoc`, `sup` (union), `combine`
  (information join), `meet`, `best` (the greatest sound simulator), `frame` (lift along an
  inclusion of locations), `lift` (along an embedding), `liftCmd` (along a map of commands).
  `PSim` has an oracle (the `nd.undef` import): `PSim.Sound` (every oracle answer is allowed
  by the reference), `PSim.SoundSome` (angelic: some answer is), `PSim.Complete` (every
  reference successor is some answer).

* `Machine.ofStep` (a deterministic `S → Option S` ISA, e.g. `Open9.isa.step`) and `Prog.loop`
  (run to completion: `Reaches`).
* `WasmSim` (derived, superseded by `Silmaril.Sim.Wasm.ExportSim`): a store machine, and
  `WasmSim.Obligations`: soundness as one partial-correctness triple per export.

Theorems: `Silmaril/Sim/Core/Thms.lean` (proofs under `Silmaril/Proofs/Sim/Core/`).
-/

@[expose] public section

namespace Silmaril.Sim

/-! ## Partial states -/

/-- A partial state: a value for some locations; `none` means unmodelled or undefined. -/
abbrev PState (L V : Type) : Type := L → Option V

namespace PState

variable {L L' V : Type}

/-- The everywhere-undefined state. -/
def bot : PState L V := fun _ => none

/-- A total state as a partial one. -/
def ofTotal (s : L → V) : PState L V := fun l => some (s l)

/-- The information order: `q` agrees with every value `p` defines. -/
def Le (p q : PState L V) : Prop := ∀ l v, p l = some v → q l = some v

/-- Two partial states agree where both are defined. -/
def Compat (p q : PState L V) : Prop := ∀ l v w, p l = some v → q l = some w → v = w

/-- Information join: `p`'s value where defined, else `q`'s (the least upper bound of
compatible states). -/
def join (p q : PState L V) : PState L V := fun l =>
  match p l with
  | some v => some v
  | none => q l

/-- Information meet: the values on which `p` and `q` agree. -/
def meet [DecidableEq V] (p q : PState L V) : PState L V := fun l =>
  if p l = q l then p l else none

/-- Restriction along a map of locations (`e : L → L'`, typically an inclusion). -/
def comap (e : L → L') (p : PState L' V) : PState L V := fun l => p (e l)

/-- `p` is defined on every location of `M`. -/
def DefinedOn (p : PState L V) (M : L → Prop) : Prop := ∀ l, M l → ∃ v, p l = some v

/-- `p` is total. -/
def Total (p : PState L V) : Prop := ∀ l, ∃ v, p l = some v

/-- `p` and `q` are equal on `M`. -/
def EqOn (M : L → Prop) (p q : PState L V) : Prop := ∀ l, M l → p l = q l

/-- Frame: `q` on the locations in `M`, `p` elsewhere. -/
noncomputable def override (M : L → Prop) (q p : PState L V) : PState L V := by
  classical
  exact fun l => if M l then q l else p l

/-- Write `q : PState L V` back along `e : L → L'`: `q` on the image of `e`, `p` elsewhere
(meaningful for injective `e`). -/
noncomputable def pushAlong (e : L → L') (q : PState L V) (p : PState L' V) : PState L' V := by
  classical
  exact fun l' => if h : ∃ l, e l = l' then q (Classical.choose h) else p l'

/-- An upward-closed predicate on partial states (an assertion about *defined* values). -/
def Mono (P : PState L V → Prop) : Prop := ∀ p q, Le p q → P p → P q

end PState

/-- The information order on partial states. -/
scoped infix:50 " ⊑ " => PState.Le

/-! ## Reflexive-transitive closure -/

/-- Reflexive-transitive closure (zero or more steps). -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star r a a
  | step {a b c : α} : r a b → Star r b c → Star r a c

/-! ## Programs -/

/-- Programs over commands `C`, with guards on the view `PState L V`. -/
inductive Prog (C L V : Type) : Type where
  /-- Do nothing. -/
  | skip
  /-- One command (an instruction, a syscall, a simulator method). -/
  | cmd (c : C)
  /-- Continue only if the view satisfies `g`. -/
  | test (g : PState L V → Prop)
  /-- Sequential composition. -/
  | seq (p q : Prog C L V)
  /-- Nondeterministic choice. -/
  | choice (p q : Prog C L V)
  /-- Zero or more iterations. -/
  | star (p : Prog C L V)
  /-- Nondeterministic choice of a value (data flow: read a value with a guard, use it in
  later commands). -/
  | pick (k : V → Prog C L V)

namespace Prog

variable {C C' C'' L L' L'' V : Type}

/-- Substitute programs for commands and rename locations in guards. -/
def subst (e : L → L') (σ : C → Prog C' L' V) : Prog C L V → Prog C' L' V
  | skip => skip
  | cmd c => σ c
  | test g => test fun q => g (PState.comap e q)
  | seq p q => seq (subst e σ p) (subst e σ q)
  | choice p q => choice (subst e σ p) (subst e σ q)
  | star p => star (subst e σ p)
  | pick k => pick fun v => subst e σ (k v)

/-- Rename commands and locations. -/
def map (e : L → L') (f : C → C') : Prog C L V → Prog C' L' V := subst e fun c => cmd (f c)

/-- `if g₁ then p else q` with an explicit guard `g₂` for the else branch (both guards
upward closed in practice, e.g. `ZF = some 1` and `ZF = some 0`). -/
def ite (g₁ g₂ : PState L V → Prop) (p q : Prog C L V) : Prog C L V :=
  choice (seq (test g₁) p) (seq (test g₂) q)

/-- `while g₁ do p` with exit guard `g₂`. -/
def whileDo (g₁ g₂ : PState L V → Prop) (p : Prog C L V) : Prog C L V :=
  seq (star (seq (test g₁) p)) (test g₂)

/-- The sequence of a list of commands (a straight-line block). -/
def block : List C → Prog C L V
  | [] => skip
  | c :: cs => seq (cmd c) (block cs)

/-- Run to completion: any number of steps of the single command (`Reaches` for `ofStep`). -/
def loop : Prog Unit L V := star (cmd ())

/-- Nondeterministic choice among a list of programs (`skip`-free: the empty list blocks). -/
def choiceList : List (Prog C L V) → Prog C L V
  | [] => test fun _ => False
  | [p] => p
  | p :: ps => choice p (choiceList ps)

/-- **A block graph** (the reduction's L-form with control flow: a `loop` + `br_table`
dispatcher, or a structured CFG): repeat one of the guarded blocks (each typically
`seq (test (pc = i)) body_i`, the body ending with the jump), then leave when `exit` holds. -/
def cfg (blocks : List (Prog C L V)) (exit : PState L V → Prop) : Prog C L V :=
  seq (star (choiceList blocks)) (test exit)

/-- Every guard of the program satisfies `T`. -/
def AllTests (T : (PState L V → Prop) → Prop) : Prog C L V → Prop
  | skip => True
  | cmd _ => True
  | test g => T g
  | seq p q => AllTests T p ∧ AllTests T q
  | choice p q => AllTests T p ∧ AllTests T q
  | star p => AllTests T p
  | pick k => ∀ v, AllTests T (k v)

/-- Every guard is upward closed in the information order. -/
def MonoTests (p : Prog C L V) : Prop := AllTests PState.Mono p

end Prog

/-! ## Machines -/

/-- A machine over commands `C`, observed through a partial view of locations `L`. Both
simulators and reference ISAs are machines. -/
structure Machine (C L V : Type) where
  /-- The (hidden) state: a Wasm store and host state, an ISA machine state, … -/
  St : Type
  /-- The observable part. -/
  view : St → PState L V
  /-- One command, as a relation (nondeterminism: oracles, environments, undefined values). -/
  step : C → St → St → Prop

namespace Machine

variable {C C' L L' V : Type}

/-- The relational semantics of a program. -/
def Sem (M : Machine C L V) : Prog C L V → M.St → M.St → Prop
  | .skip => fun a b => a = b
  | .cmd c => M.step c
  | .test g => fun a b => a = b ∧ g (M.view a)
  | .seq p q => fun a c => ∃ b, Sem M p a b ∧ Sem M q b c
  | .choice p q => fun a b => Sem M p a b ∨ Sem M q a b
  | .star p => Star (Sem M p)
  | .pick k => fun a b => ∃ v, Sem M (k v) a b

/-- A machine seen through a substitution: command `c` runs the program `σ c`, the view is
restricted along `e`. -/
def reduct (e : L → L') (σ : C → Prog C' L' V) (M : Machine C' L' V) : Machine C L V where
  St := M.St
  view a := PState.comap e (M.view a)
  step c := M.Sem (σ c)

/-- The machine restricted to states satisfying `I` (steps to states outside `I` are
dropped; use it with an invariant `I`, e.g. `live`). -/
def restrict (M : Machine C L V) (I : M.St → Prop) : Machine C L V where
  St := {a // I a}
  view a := M.view a.1
  step c a b := M.step c a.1 b.1

/-- Deterministic: at most one successor per command. -/
def Deterministic (M : Machine C L V) : Prop :=
  ∀ c a b b', M.step c a b → M.step c a b' → b = b'

/-- Command `c` leaves the locations outside `K` unchanged. -/
def Frames (M : Machine C L V) (c : C) (K : L → Prop) : Prop :=
  ∀ a b, M.step c a b → ∀ l, ¬ K l → M.view b l = M.view a l

/-- A deterministic partial machine with one command (`step : S → Option S`, e.g.
`Silmaril.X86.SegVC.Isa.step` of `Open9.isa`, or an RV64 step), observed through `view`. -/
def ofStep {S : Type} (step : S → Option S) (view : S → PState L V) : Machine Unit L V :=
  ⟨S, view, fun _ s t => step s = some t⟩

/-! ### Properties of programs -/

/-- **Angelic total correctness** on hidden states: from every `P`-state some run of `p`
ends in a `Q`-related state. -/
def HAngelic (M : Machine C L V) (P : M.St → Prop) (p : Prog C L V)
    (Q : M.St → M.St → Prop) : Prop :=
  ∀ a, P a → ∃ b, M.Sem p a b ∧ Q a b

/-- **Demonic partial correctness** on hidden states: every run of `p` from a `P`-state ends
in a `Q`-related state. -/
def HDemonic (M : Machine C L V) (P : M.St → Prop) (p : Prog C L V)
    (Q : M.St → M.St → Prop) : Prop :=
  ∀ a b, P a → M.Sem p a b → Q a b

/-- Some run of `p` exists from every `P`-state. -/
def HProgress (M : Machine C L V) (P : M.St → Prop) (p : Prog C L V) : Prop :=
  ∀ a, P a → ∃ b, M.Sem p a b

/-- Angelic total correctness, stated on views. -/
def Angelic (M : Machine C L V) (P : PState L V → Prop) (p : Prog C L V)
    (Q : PState L V → PState L V → Prop) : Prop :=
  M.HAngelic (fun a => P (M.view a)) p (fun a b => Q (M.view a) (M.view b))

/-- Demonic partial correctness, stated on views. -/
def Demonic (M : Machine C L V) (P : PState L V → Prop) (p : Prog C L V)
    (Q : PState L V → PState L V → Prop) : Prop :=
  M.HDemonic (fun a => P (M.view a)) p (fun a b => Q (M.view a) (M.view b))

/-- **Demonic total reachability** for command `c` (the shape of `RelIsa.Must`): every run of
`c`-steps from `a`, taken only from `G`-states and never from a `stop` state, terminates in a
`Q`-state. Inductive, so termination is built in. -/
inductive Must (M : Machine C L V) (c : C) (stop : M.St → Prop) (G Q : M.St → Prop) :
    M.St → Prop
  | done {a : M.St} : Q a → Must M c stop G Q a
  | step {a : M.St} : G a → ¬ stop a → (∀ b, M.step c a b → Must M c stop G Q b) →
      Must M c stop G Q a

/-- Progress, stated on views. -/
def Progress (M : Machine C L V) (P : PState L V → Prop) (p : Prog C L V) : Prop :=
  M.HProgress (fun a => P (M.view a)) p

end Machine

/-! ## Soundness, completeness, equivalence -/

/-- **A forward simulation** of `A` by `B` along `R`, with no condition on views: the
step-matching part of `Simulation` (and of `Silmaril.Sim.Reduce.SoundSim`). -/
structure FwdSim {C L V : Type} (A B : Machine C L V) where
  /-- The simulation relation (simulator state, reference state). -/
  R : A.St → B.St → Prop
  /-- Every simulator step is a reference step. -/
  step : ∀ {c a a' b}, R a b → A.step c a a' → ∃ b', B.step c b b' ∧ R a' b'

/-- **A sound simulator.** `A` (the simulator) is simulated by `B` (the reference) along `R`:
related states agree on everything `A` defines, every `A`-step is matched by a `B`-step with
the same command, and every `B`-state can be loaded into `A` with the same view. -/
structure Simulation {C L V : Type} (A B : Machine C L V) extends FwdSim A B where
  /-- What the simulator shows is true of the reference. -/
  view_le : ∀ {a b}, R a b → A.view a ⊑ B.view b
  /-- Every reference state can be loaded into the simulator (the `set` export). -/
  load : ∀ b, ∃ a, R a b ∧ A.view a = B.view b

/-- `A` is a sound simulator of `B`. -/
def Sound {C L V : Type} (A B : Machine C L V) : Prop := Nonempty (Simulation A B)

/-- A simulation is **exact** when related states show the same view: the simulator has a value
for every location (undefined values drawn from the oracle, `nd.undef`). Exact simulations
transfer properties with arbitrary guards and postconditions (branches on flags). -/
def Simulation.Exact {C L V : Type} {A B : Machine C L V} (S : Simulation A B) : Prop :=
  ∀ {a b}, S.R a b → A.view a = B.view b

/-- `A` is an exact sound simulator of `B`. -/
def ExactSound {C L V : Type} (A B : Machine C L V) : Prop := ∃ S : Simulation A B, S.Exact

/-- **A complete simulator.** Every `B`-step is matched by an `A`-step (for some oracle
answer), with equal views. -/
structure CoSimulation {C L V : Type} (A B : Machine C L V) where
  /-- The relation (simulator state, reference state). -/
  R : A.St → B.St → Prop
  /-- Related states show the same view. -/
  view_eq : ∀ {a b}, R a b → A.view a = B.view b
  /-- Every reference step is a simulator step. -/
  step : ∀ {c a b b'}, R a b → B.step c b b' → ∃ a', A.step c a a' ∧ R a' b'
  /-- Every reference state can be loaded. -/
  load : ∀ b, ∃ a, R a b

/-- `A` is a complete simulator of `B`. -/
def Complete {C L V : Type} (A B : Machine C L V) : Prop := Nonempty (CoSimulation A B)

/-- **Equivalent machines** (a bisimulation with equal views, total on both sides): two
state representations of one simulator (globals vs. `user_regs_struct` in memory). -/
structure Equiv {C L V : Type} (A B : Machine C L V) where
  /-- The relation. -/
  R : A.St → B.St → Prop
  /-- Related states show the same view. -/
  view_eq : ∀ {a b}, R a b → A.view a = B.view b
  /-- Forward steps. -/
  fwd : ∀ {c a a' b}, R a b → A.step c a a' → ∃ b', B.step c b b' ∧ R a' b'
  /-- Backward steps. -/
  bwd : ∀ {c a b b'}, R a b → B.step c b b' → ∃ a', A.step c a a' ∧ R a' b'
  /-- Every `B`-state has a related `A`-state. -/
  load : ∀ b, ∃ a, R a b
  /-- Every `A`-state has a related `B`-state. -/
  store : ∀ a, ∃ b, R a b

/-! ## Partial-state simulators -/

/-- A partial-state simulator as a relation: `s c p p'` when the simulator, run on the
partial state `p`, executes `c` and shows `p'` (for some oracle answer). -/
abbrev PRel (C L V : Type) : Type := C → PState L V → PState L V → Prop

namespace PRel

variable {C C' L L' V : Type}

/-- The simulator as a machine whose state is its view. -/
def toMachine (s : PRel C L V) : Machine C L V := ⟨PState L V, id, s⟩

/-- **Soundness** of a partial-state simulator: whenever it steps from a partial state true of
a reference state `b`, the reference steps to a state of which the result is true. Reading
an undefined location makes a well-behaved simulator not step (status 2). Unmodelled
locations are framed (copied: the reference must keep them) or havocked (`none`). -/
def Sound (s : PRel C L V) (B : Machine C L V) : Prop :=
  ∀ c p p' b, p ⊑ B.view b → s c p p' → ∃ b', B.step c b b' ∧ p' ⊑ B.view b'

/-- Soundness for one command (one simulator method): an independent problem. -/
def SoundAt (s : PRel C L V) (B : Machine C L V) (c : C) : Prop :=
  ∀ p p' b, p ⊑ B.view b → s c p p' → ∃ b', B.step c b b' ∧ p' ⊑ B.view b'

/-- **Refinement**: `t` steps wherever `s` does, at least as informatively. -/
def Le (s t : PRel C L V) : Prop := ∀ c p p', s c p p' → ∃ p'', t c p p'' ∧ p' ⊑ p''

/-- The simulator that never steps (models nothing): the bottom. -/
def bot : PRel C L V := fun _ _ _ => False

/-- The simulator that steps everywhere and knows nothing afterwards. -/
def havoc : PRel C L V := fun _ _ p' => p' = PState.bot

/-- Union of behaviours (least upper bound in `Le`). -/
def sup (s t : PRel C L V) : PRel C L V := fun c p p' => s c p p' ∨ t c p p'

/-- Union of a family. -/
def sSup (F : PRel C L V → Prop) : PRel C L V := fun c p p' => ∃ s, F s ∧ s c p p'

/-- **Combination** of two simulators (e.g. a GPR simulator and a flags simulator): both step,
and the results are joined. Sound when the reference is deterministic. -/
def combine (s t : PRel C L V) : PRel C L V :=
  fun c p p' => ∃ p₁ p₂, s c p p₁ ∧ t c p p₂ ∧ p' = PState.join p₁ p₂

/-- Meet (greatest lower bound in `Le`): both step, keep what they agree on. -/
def meet [DecidableEq V] (s t : PRel C L V) : PRel C L V :=
  fun c p p' => ∃ p₁ p₂, s c p p₁ ∧ t c p p₂ ∧ p' = PState.meet p₁ p₂

/-- **The best simulator** of `B`: from `p`, every result that is true after some step of
every reference state of which `p` is true. The greatest sound simulator. -/
def best (B : Machine C L V) : PRel C L V :=
  fun c p p' => ∀ b, p ⊑ B.view b → ∃ b', B.step c b b' ∧ p' ⊑ B.view b'

/-- **Frame**: run `s`, keep its results on `K` and the old values elsewhere. -/
noncomputable def frame (K : L → Prop) (s : PRel C L V) : PRel C L V :=
  fun c p p' => ∃ q, s c p q ∧ p' = PState.override K q p

/-- **Lift** along an embedding of locations `e : L → L'`: run `s` on the restriction and
write its results back, keeping the other locations. -/
noncomputable def lift (e : L → L') (s : PRel C L V) : PRel C L' V :=
  fun c p p' => ∃ q, s c (PState.comap e p) q ∧ p' = PState.pushAlong e q p

/-- Lift along a map of commands `f : C → C'` (instruction coverage grows). -/
def liftCmd (f : C → C') (s : PRel C L V) : PRel C' L V :=
  fun c' p p' => ∃ c, f c = c' ∧ s c p p'

/-- The reference with commands renamed along `f` (used with `liftCmd`). -/
def _root_.Silmaril.Sim.Machine.comapCmd (f : C → C') (B : Machine C' L V) : Machine C L V :=
  ⟨B.St, B.view, fun c => B.step (f c)⟩

/-- The reference with its view restricted along `e` (used with `lift`). -/
def _root_.Silmaril.Sim.Machine.comapLoc (e : L → L') (B : Machine C L' V) : Machine C L V :=
  ⟨B.St, fun b => PState.comap e (B.view b), B.step⟩

end PRel

/-- A partial-state simulator with oracle answers `O` (the `nd.undef` import): a partial
function; `none` is "not supported here" (status 2). -/
structure PSim (C L V O : Type) where
  /-- Execute one command with an oracle answer. -/
  step : C → O → PState L V → Option (PState L V)

namespace PSim

variable {C L V O : Type}

/-- The behaviours over all oracle answers. -/
def rel (S : PSim C L V O) : PRel C L V := fun c p p' => ∃ o, S.step c o p = some p'

/-- The simulator as a machine. -/
def toMachine (S : PSim C L V O) : Machine C L V := S.rel.toMachine

/-- **Demonic oracle soundness**: for *every* oracle answer, the reference allows the result. -/
def Sound (S : PSim C L V O) (B : Machine C L V) : Prop :=
  ∀ c o p p' b, p ⊑ B.view b → S.step c o p = some p' → ∃ b', B.step c b b' ∧ p' ⊑ B.view b'

/-- **Angelic oracle soundness**: when the simulator supports `p`, *some* oracle answer gives a
result the reference allows. -/
def SoundSome (S : PSim C L V O) (B : Machine C L V) : Prop :=
  ∀ c p b, p ⊑ B.view b → (∃ o p', S.step c o p = some p') →
    ∃ o p' b', S.step c o p = some p' ∧ B.step c b b' ∧ p' ⊑ B.view b'

/-- **Completeness**: every reference successor is the simulator's result for some oracle
answer, from the reference's own view. -/
def Complete (S : PSim C L V O) (B : Machine C L V) : Prop :=
  ∀ c b b', B.step c b b' → ∃ o, S.step c o (B.view b) = some (B.view b')

/-- **Exact oracle soundness**: from a reference state's own view, every result of the
simulator (for every oracle answer) is the view of some reference successor. With it, a
simulator that draws undefined values from the oracle can branch on them. -/
def SoundExact (S : PSim C L V O) (B : Machine C L V) : Prop :=
  ∀ c o b p', S.step c o (B.view b) = some p' → ∃ b', B.step c b b' ∧ p' = B.view b'

/-- The simulator with the oracle fixed to one answer function. -/
def fix (S : PSim C L V O) (o : O) : PSim C L V Unit := ⟨fun c _ p => S.step c o p⟩

end PSim

/-! ## The interface of a concrete Wasm simulator -/

/-- **A Wasm simulator as a store machine** (derived form, superseded). `Store` is the Wasm
store together with the state of the opaque imports; `get` is the meaning of the `get`/`modelled`
exports; `call c` relates the store before and after a call of the export implementing command
`c`. A `WasmSim` is just a `Machine` (`WasmSim.toMachine`), and its `Obligations` feed
`Simulation.ofMethods`. New code uses `Silmaril.Sim.Wasm.ExportSim` (`ExportSim.toMachine`,
`ExportSim.Cert.simulation`); this structure is kept because existing statements mention
`ExportSim.toWasmSim`. -/
structure WasmSim (C L V : Type) where
  /-- Wasm store and import state. -/
  Store : Type
  /-- The view through the `get` export (`none` where `modelled` is `0` or undefined). -/
  get : Store → PState L V
  /-- The call relation of the export implementing a command. -/
  call : C → Store → Store → Prop

/-- The Wasm simulator as a machine. -/
def WasmSim.toMachine {C L V : Type} (W : WasmSim C L V) : Machine C L V :=
  ⟨W.Store, W.get, W.call⟩

/-- **The soundness obligations of a Wasm simulator, one Wasm problem per export.** A relation
`R` between stores and reference states; `get` shows only true values; every reference state
can be loaded (`set`); and for every command `c` and every reference state `b` (a ghost), the
export implementing `c` meets the *partial-correctness* triple
`{R · b} call c {∃ b', B.step c b b' ∧ R · b'}`: the shape of `Silmaril.Wasm.Logic.Hoare.FSpecValid`
and `Silmaril.Wasm.Verify.Verified` (`Simulation.ofMethods` builds the simulation). -/
structure WasmSim.Obligations {C L V : Type} (W : WasmSim C L V) (B : Machine C L V) where
  /-- The relation (store, reference state). -/
  R : W.Store → B.St → Prop
  /-- `get` shows only true values. -/
  view_le : ∀ {a b}, R a b → W.get a ⊑ B.view b
  /-- Loading. -/
  load : ∀ b, ∃ a, R a b ∧ W.get a = B.view b
  /-- Per-export partial correctness. -/
  method : ∀ c b, W.toMachine.HDemonic (fun a => R a b) (.cmd c)
    (fun _ a' => ∃ b', B.step c b b' ∧ R a' b')

end Silmaril.Sim

end

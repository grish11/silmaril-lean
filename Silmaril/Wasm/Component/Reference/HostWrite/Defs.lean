module

public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs

/-!
# Host-state writes along machine runs: definitions

The host state `m.host` of a configuration of the reference machine changes only by the program
operation `hostSet s` (`Machine.Step.hostSet`). This module defines a program and configuration
invariant that bounds those writes by a relation `Ext` between the host state just read and the
state written, and so characterises how the host state can evolve along machine runs.

* `HostSafe Ext c p`: the host writes of the program `p` are allowed by `Ext`. Every operation
  other than `hostGet`/`hostSet` is accepted; `hostGet` may be followed, **immediately**, by a
  `hostSet s'` of a state related by `Ext` to the state `s` just read (`c = some s` records that
  the last operation of `p` read `s`; `c = none` that it did not). A `hostSet` that does not
  immediately follow a `hostGet` is rejected, so a write never uses a stale read: the machine
  runs the head program of the control chain, and between a `hostGet` step and the `hostSet`
  step right after it no other step happens. Programs that never write the host state are
  `HostSafe` (`P.InvW (fun _ => True) (fun _ => False)`, `Canon.Effects`).
* `FocusSafe`, `SegSafe`, `ActSafe`, `CfgSafe Ext m`: every program of the configuration `m`
  (running activations, their pending continuations, the saved activations of blocked threads)
  is `HostSafe` with no pending read, except the running program of the head activation, which
  may have just read the current host state `m.host`.
* `DispatchSafe Ext dispatch`, `HostImplSafe Ext host`: every program of a dispatcher, resp. of
  a host implementation, is `HostSafe`.
* `logExt`: the relation of the logging host `HLinked2.logG g`: the log strictly grows by
  appending, `s.2` a strict prefix of `s'.2`.

The theorems are in `Silmaril.Wasm.Component.Reference.HostWrite.Thms`: every program of the
reference dispatcher `Canon.dispatch` is `HostSafe` for a `HostSafe` host, the answering host
`answerImplS (logG g)` is `HostSafe` for `logExt`, every machine step keeps `CfgSafe`, and along a
step the host state is unchanged or related by `Ext`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

/-- An operation that neither reads nor writes the host state. -/
def Op.Plain : Op E σ → Prop
  | .hostGet => False
  | .hostSet _ => False
  | _ => True

/-- **The host writes of a program are allowed by `Ext`**: with `c = some s` the program has just
read the host state `s`, and may then write a state `s'` with `Ext s s'`, as its next operation;
with `c = none` it may not write before reading. -/
inductive HostSafe (Ext : σ → σ → Prop) {α : Type} : Option σ → P E σ α → Prop where
  | pure (c : Option σ) (a : α) : HostSafe Ext c (Prog.pure a)
  | op (c : Option σ) {o : Op E σ} {k : (Eff E σ).Resp o → P E σ α} :
      o.Plain → (∀ r, HostSafe Ext none (k r)) → HostSafe Ext c (.op (S := Eff E σ) o k)
  | get (c : Option σ) {k : σ → P E σ α} :
      (∀ s, HostSafe Ext (some s) (k s)) → HostSafe Ext c (.op (S := Eff E σ) .hostGet k)
  | set {s s' : σ} {k : Unit → P E σ α} :
      Ext s s' → HostSafe Ext none (k ()) →
        HostSafe Ext (some s) (.op (S := Eff E σ) (.hostSet s') k)

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-- The programs of a focus are host-safe, the running program with the pending read `c`. -/
def FocusSafe (Ext : σ → σ → Prop) (c : Option σ) : Focus E σ → Prop
  | .prog p => HostSafe Ext c p
  | .core _ k => ∀ vs, HostSafe Ext none (k vs)

/-- The programs of a pending continuation are host-safe. -/
def SegSafe (Ext : σ → σ → Prop) : Seg E σ → Prop
  | .prog k => ∀ r, HostSafe Ext none (k r)
  | .core _ k => ∀ vs, HostSafe Ext none (k vs)

/-- The programs of an activation are host-safe, its running program with the pending read `c`. -/
def ActSafe (Ext : σ → σ → Prop) (c : Option σ) (a : Activation E σ) : Prop :=
  FocusSafe Ext c a.focus ∧ ∀ g ∈ a.segs, SegSafe Ext g

/-- The activations of a control chain are host-safe, the head one with the pending read `c`. -/
def CtlSafe (Ext : σ → σ → Prop) (c : Option σ) : List (Activation E σ) → Prop
  | [] => True
  | a :: rest => ActSafe Ext c a ∧ ∀ b ∈ rest, ActSafe Ext none b

/-- **Every program of a configuration is host-safe**; the running program of the head
activation may have just read the current host state. -/
def CfgSafe (Ext : σ → σ → Prop) (m : Config E σ) : Prop :=
  CtlSafe Ext (some m.host) m.ctl ∧ ∀ t a, m.cont? t = some a → ActSafe Ext none a

/-- Every program of a dispatcher is host-safe. -/
def DispatchSafe (Ext : σ → σ → Prop) (dispatch : Call E → P E σ (Ret E)) : Prop :=
  ∀ c, HostSafe Ext none (dispatch c)

/-- Every program of a host implementation is host-safe. -/
structure HostImplSafe (Ext : σ → σ → Prop) (host : HostImpl E σ) : Prop where
  funcs : ∀ fn c, HostSafe Ext none (host.funcs fn c)
  embedder : ∀ n ft args, HostSafe Ext none (host.embedder n ft args)
  threadBody : ∀ fn t, HostSafe Ext none (host.threadBody fn t)
  buffer : ∀ op, HostSafe Ext none (host.buffer op)
  cancel : ∀ n, HostSafe Ext none (host.cancel n)

/-- The host-frame programs of a trace are host-safe. -/
def RunSafe (Ext : σ → σ → Prop) (tr : List (Label E σ)) : Prop :=
  ∀ p, Label.host (.run p) ∈ tr → HostSafe Ext none p

end Silmaril.Wasm.Component.Machine

namespace Silmaril.Wasm.Component.Reference

/-- **The relation of a logging host**: the log of `s'` strictly extends that of `s`. -/
def logExt {σ ε : Type} (s s' : σ × List ε) : Prop :=
  s.2 <+: s'.2 ∧ s.2.length < s'.2.length

end Silmaril.Wasm.Component.Reference

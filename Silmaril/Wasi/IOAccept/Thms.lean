module

public import Silmaril.Wasi.IOAccept.Defs
public import Silmaril.Semantics.Accept.IO.Thms
public import Silmaril.Wasi.Component.Accept.Thms
import Silmaril.Proofs.Wasi.IOAccept.Basic

/-! # Relational I/O acceptance of component traces: theorems

* **Refinement and equivalence**: a refinement has fewer runs (`ioRuns_mono`,
  `entryIORuns_mono`); components with the same named traces (`Silmaril.Wasi.Accept.Traces`),
  in any worlds, have the same runs (`ioRuns_eq_of_traces`, `entryIORuns_eq_of_traces`), hence
  the same `triggers`, `episodes`, `retTriggers` and `returns`.
* **Scopes of legal plays** (the structural bridge): the tags of a legal play are `Shallow`
  (`shallow_of_legal`): no export call starts inside another one; the next export event after
  an export call is the return or trap of that same call (`ret_after_call`). The scopes that
  `bracket` assigns to a shallow tag list are exactly its `blocks` (`localView_bracket_of_shallow`,
  `exists_localView_bracket`); the blocks of a decoded named trace are its call blocks
  `wblocks`, decoded (`blocks_filterMap_tag`). So each import event of a legal play belongs to
  the scope of the most recent export call, and the runs of a component are the windows of the
  call blocks of its plays (`mem_ioRuns`, `mem_entryIORuns`).
* **Soundness**: an input `a` triggers an output `b` only through an input event followed in
  the same play by an output event (`triggers_ioRuns_sound`), and similarly for returns
  (`returns_ioRuns_sound`) and entry returns (`returns_entryIORuns_sound`); event decodings
  are inverted by `locOf_eq_out` and `locOf_eq_exit`.
* **The unary reading**: an output triggered under `importIO inp out decI decO` is accepted
  through the import `out` (`mem_importAccepted_of_triggers`, `Silmaril.Wasi.Accept`).

The longer proofs are in `Silmaril.Proofs.Wasi.IOAccept.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasi.IOAccept

open Silmaril.Games Silmaril.Accept.IO Silmaril.Wasi.Accept
open Silmaril.Wasm.Component (Val)
open scoped List

variable {X I O C : Type} {Im Ex Im' Ex' : Set FnName}

/-! ## Refinement and equivalence -/

/-- A refinement has fewer input-window runs. -/
theorem ioRuns_mono {σ τ : Strategy (nsig Im) (nsig Ex)} (h : σ ≤ τ) (ρ : Roles X I O C) :
    ioRuns σ ρ ⊆ ioRuns τ ρ :=
  inputRunsOf_mono (Set.image_mono (traces_mono h))

/-- A refinement has fewer entry runs. -/
theorem entryIORuns_mono {σ τ : Strategy (nsig Im) (nsig Ex)} (h : σ ≤ τ)
    (ρ : Roles X I O C) : entryIORuns σ ρ ⊆ entryIORuns τ ρ :=
  entryRunsOf_mono (Set.image_mono (traces_mono h))

/-- Components with the same named traces have the same input-window runs. -/
theorem ioRuns_eq_of_traces {σ : Strategy (nsig Im) (nsig Ex)}
    {τ : Strategy (nsig Im') (nsig Ex')} (h : Traces σ = Traces τ) (ρ : Roles X I O C) :
    ioRuns σ ρ = ioRuns τ ρ := by
  unfold ioRuns; rw [h]

/-- Components with the same named traces have the same entry runs. -/
theorem entryIORuns_eq_of_traces {σ : Strategy (nsig Im) (nsig Ex)}
    {τ : Strategy (nsig Im') (nsig Ex')} (h : Traces σ = Traces τ) (ρ : Roles X I O C) :
    entryIORuns σ ρ = entryIORuns τ ρ := by
  unfold entryIORuns; rw [h]

/-! ## Scopes of legal plays -/

/-- **Legal plays are shallow**: the tags of a legal play follow the depth-one automaton. No
export call starts while another is running (the Games model has no reentrant callbacks). -/
theorem shallow_of_legal (ρ : Roles X I O C) {s : List (Move (nsig Im) (nsig Ex))}
    (hs : Legal s) : Shallow false ((wtrace s).filterMap (tag ρ)) :=
  Proofs.Wasi.IOAccept.shallow_of_legal ρ hs

/-- **Between an export call and its return there is no other export event**: in a legal
play, the next export event after `call f a` is `ret f a r` for some `r`. -/
theorem ret_after_call {s : List (Move (nsig Im) (nsig Ex))} (hs : Legal s)
    {u v w : List WEv} {f : FnName} {a : List Val} {e : WEv}
    (h : wtrace s = u ++ .call f a :: (v ++ e :: w)) (hv : ∀ e' ∈ v, e'.isExp = false)
    (he : e.isExp = true) : ∃ r, e = .ret f a r :=
  Proofs.Wasi.IOAccept.ret_after_call hs h hv he

/-- **Every scope of a shallow tag list is one of its blocks** (or empty). -/
theorem localView_bracket_of_shallow {ts : List (Tag X I O C)} (h : Shallow false ts) (k : ℕ) :
    localView k (bracket ts) = [] ∨ localView k (bracket ts) ∈ blocks ts :=
  (Proofs.Wasi.IOAccept.views_of_shallow ts h 0).1 k

/-- **Every block of a shallow tag list is a scope.** -/
theorem exists_localView_bracket {ts : List (Tag X I O C)} (h : Shallow false ts)
    {l : List (Loc X I O C)} (hl : l ∈ blocks ts) : ∃ k, localView k (bracket ts) = l :=
  (Proofs.Wasi.IOAccept.views_of_shallow ts h 0).2 l hl

/-- The blocks of a decoded named trace are its decoded call blocks. -/
theorem blocks_filterMap_tag (ρ : Roles X I O C) (t : List WEv) :
    blocks (t.filterMap (tag ρ)) = (wblocks t).map (·.filterMap (locOf ρ)) :=
  Proofs.Wasi.IOAccept.blocks_filterMap ρ t

/-- **The input-window runs of a legal play are the windows of its call blocks.** -/
theorem mem_inputRuns_decode {s : List (Move (nsig Im) (nsig Ex))} (hs : Legal s)
    (ρ : Roles X I O C) (r : Run I O C) :
    r ∈ inputRuns (decode (tag ρ) (wtrace s)) ↔
      ∃ b ∈ wblocks (wtrace s), r ∈ windows (b.filterMap (locOf ρ)) :=
  Proofs.Wasi.IOAccept.mem_inputRuns_decode hs ρ r

/-- **The entry runs of a legal play are those of its call blocks.** -/
theorem mem_entryRuns_decode {s : List (Move (nsig Im) (nsig Ex))} (hs : Legal s)
    (ρ : Roles X I O C) (r : Run X O C) :
    r ∈ entryRuns (decode (tag ρ) (wtrace s)) ↔
      ∃ b ∈ wblocks (wtrace s), entryRun (b.filterMap (locOf ρ)) = some r :=
  Proofs.Wasi.IOAccept.mem_entryRuns_decode hs ρ r

/-- **The input-window runs of a component**, read off the call blocks of its plays. -/
theorem mem_ioRuns (σ : Strategy (nsig Im) (nsig Ex)) (ρ : Roles X I O C) (r : Run I O C) :
    r ∈ ioRuns σ ρ ↔
      ∃ s ∈ σ, ∃ b ∈ wblocks (wtrace s), r ∈ windows (b.filterMap (locOf ρ)) :=
  Proofs.Wasi.IOAccept.mem_ioRuns σ ρ r

/-- **The entry runs of a component**, read off the call blocks of its plays. -/
theorem mem_entryIORuns (σ : Strategy (nsig Im) (nsig Ex)) (ρ : Roles X I O C)
    (r : Run X O C) : r ∈ entryIORuns σ ρ ↔
      ∃ s ∈ σ, ∃ b ∈ wblocks (wtrace s), entryRun (b.filterMap (locOf ρ)) = some r :=
  Proofs.Wasi.IOAccept.mem_entryIORuns σ ρ r

/-! ## Soundness -/

/-- An output decoding comes from an import call with that output role. -/
theorem locOf_eq_out {ρ : Roles X I O C} {e : WEv} {b : O} (h : locOf ρ e = some (.out b)) :
    ∃ f a, e = .req f a ∧ ρ.callOut f a = some b :=
  Proofs.Wasi.IOAccept.locOf_eq_out h

/-- A successful result decoding comes from a successful export return. -/
theorem locOf_eq_exit {ρ : Roles X I O C} {e : WEv} {c : C}
    (h : locOf ρ e = some (.exit (some c))) :
    ∃ f a res, e = .ret f a (some res) ∧ ρ.result f a res = some c :=
  Proofs.Wasi.IOAccept.locOf_eq_exit h

/-- **Triggering is sound**: `a` triggers `b` only when some play has an input event `a`
followed by an output event `b`. -/
theorem triggers_ioRuns_sound {σ : Strategy (nsig Im) (nsig Ex)} {ρ : Roles X I O C} {a : I}
    {b : O} (h : (a, b) ∈ triggers (ioRuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.inp a) ∧
      locOf ρ e₂ = some (.out b) :=
  Proofs.Wasi.IOAccept.triggers_ioRuns_sound h

/-- **Returns are sound**: `a` returns `c` only when some play has an input event `a` followed
by a successful export return decoding to `c`. -/
theorem returns_ioRuns_sound {σ : Strategy (nsig Im) (nsig Ex)} {ρ : Roles X I O C} {a : I}
    {c : C} (h : (a, c) ∈ returns (ioRuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.inp a) ∧
      locOf ρ e₂ = some (.exit (some c)) :=
  Proofs.Wasi.IOAccept.returns_ioRuns_sound h

/-- **Entry returns are sound**: `x` returns `c` only when some play has an export call
decoding to the entry `x` followed by a successful export return decoding to `c`. -/
theorem returns_entryIORuns_sound {σ : Strategy (nsig Im) (nsig Ex)} {ρ : Roles X I O C}
    {x : X} {c : C} (h : (x, c) ∈ returns (entryIORuns σ ρ)) :
    ∃ s ∈ σ, ∃ e₁ e₂, [e₁, e₂] <+ wtrace s ∧ locOf ρ e₁ = some (.enter (some x)) ∧
      locOf ρ e₂ = some (.exit (some c)) :=
  Proofs.Wasi.IOAccept.returns_entryIORuns_sound h

/-- **Triggered outputs are accepted through the output import** (the unary reading
`Silmaril.Wasi.Accept.importAccepted`). -/
theorem mem_importAccepted_of_triggers {σ : Strategy (nsig Im) (nsig Ex)} {inp out : FnName}
    {decI : List Val → Option I} {decO : List Val → Option O} {a : I} {b : O}
    (h : (a, b) ∈ triggers (ioRuns σ (importIO inp out decI decO))) :
    b ∈ importAccepted σ out decO :=
  Proofs.Wasi.IOAccept.mem_importAccepted_of_triggers h

end Silmaril.Wasi.IOAccept

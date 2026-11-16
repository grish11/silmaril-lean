module

public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.OpenStrat.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms

/-!
# Sessions of invocations with exceptions against a host (proofs)

* Generic: erasing trap stores commutes with the host restriction and the question guard
  (`eraseTrap_hostRestrict_guardT`); two store-retaining triples without plain traps are equal
  when their erasures are equal and they have the same store-keeping traps
  (`eq_of_eraseTrap_eq`): off traps, a behaviour is read back from its erasure.
* `eraseTrap_natTripleSXP`: the native session triple erases to `obsTriple Ok (NatObsXP …)`,
  by `eraseTrap_sessionTripleXP` and `obsTriple_natXP_eq`.
* `eraseTrap_coreTripleSXP`: the Core session triple erases to `obsTriple Ok (CoreObsLXP …)`.
* `natTripleSXP_eq_coreTripleSXP`: the session square. The erasures agree by the exact-log
  square (`obsTriple_eq_of_square`, `backDivXP`, `backInfXP`); the store-keeping traps by
  `wasmEvFunXPS_trap_iff`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostSessionXP

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost
open Silmaril.Games.Abstract.StratSession (eraseEnd eraseTrap NoPlainTrap)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

section Generic

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-- Erasing trap stores commutes with the host restriction and the question guard. -/
theorem eraseTrap_hostRestrict_guardT (R : HostRel E) (Ok : S → A → Prop)
    (t : ObsTriple E S A (B ⊕ PUnit.{u + 1})) :
    eraseTrap (hostRestrict R (guardT Ok t)) = hostRestrict R (guardT Ok (eraseTrap t)) := by
  refine Prod.ext (funext fun s => funext fun a => Set.ext fun x => ?_) rfl
  constructor
  · rintro ⟨y, ⟨⟨hq, hy⟩, hc⟩, rfl⟩
    exact ⟨⟨hq, y, hy, rfl⟩, hc⟩
  · rintro ⟨⟨hq, y, hy, rfl⟩, hc⟩
    exact ⟨y, ⟨⟨hq, hy⟩, hc⟩, rfl⟩

/-- Off traps, a behaviour is read back from its erasure. -/
theorem mem_iff_eraseTrap {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s : S} {a : A}
    {c : List (Call E)} {e : End S (B ⊕ PUnit.{u + 1})}
    (he : ∀ s₂, e ≠ .ret (.inr PUnit.unit) s₂) (ht : e ≠ .trap) :
    (c, e) ∈ t.1 s a ↔ (c, eraseEnd e) ∈ (eraseTrap t).1 s a := by
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨⟨c', e'⟩, h, hce⟩
    simp only [Prod.mk.injEq] at hce
    obtain ⟨rfl, hce⟩ := hce
    rcases e with ⟨b | u, s₂⟩ | _ | _
    · rcases e' with ⟨b' | u', s₂'⟩ | _ | _ <;>
        simp only [eraseEnd, End.ret.injEq, reduceCtorEq] at hce
      obtain ⟨rfl, rfl⟩ := hce
      exact h
    · exact (he s₂ rfl).elim
    · exact (ht rfl).elim
    · rcases e' with ⟨b' | u', s₂'⟩ | _ | _ <;> simp [eraseEnd] at hce
      exact h

/-- **Two store-retaining triples without plain traps are equal** when their erasures are equal
and they have the same store-keeping traps. -/
theorem eq_of_eraseTrap_eq {t t' : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (hn : NoPlainTrap t)
    (hn' : NoPlainTrap t') (he : eraseTrap t = eraseTrap t')
    (htrap : ∀ s a c s₂,
      (c, .ret (.inr PUnit.unit) s₂) ∈ t.1 s a ↔ (c, .ret (.inr PUnit.unit) s₂) ∈ t'.1 s a) :
    t = t' := by
  obtain ⟨f, p, i⟩ := t
  obtain ⟨f', p', i'⟩ := t'
  have hp : p = p' := congrArg (fun x => x.2.1) he
  have hi : i = i' := congrArg (fun x => x.2.2) he
  subst hp hi
  congr 1
  funext s a
  ext ⟨c, e⟩
  rcases e with ⟨b | u, s₂⟩ | _ | _
  · rw [mem_iff_eraseTrap (t := (f, p, i)) (by simp) (by simp),
      mem_iff_eraseTrap (t := (f', p, i)) (by simp) (by simp), he]
  · exact htrap s a c s₂
  · exact iff_of_false (hn s a c) (hn' s a c)
  · rw [mem_iff_eraseTrap (t := (f, p, i)) (by simp) (by simp),
      mem_iff_eraseTrap (t := (f', p, i)) (by simp) (by simp), he]

end Generic

variable {H : Type}

/-- **The native session triple erases to the native triple with exceptions.** -/
theorem eraseTrap_natTripleSXP (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    eraseTrap (natTripleSXP host Ok) = obsTriple Ok (fun s q => NatObsXP host s q.1 q.2) := by
  rw [natTripleSXP, eraseTrap_hostRestrict_guardT, eraseTrap_sessionTripleXP, obsTriple_natXP_eq]

/-- **The Core session triple with exceptions erases to the Core triple with exceptions.** -/
theorem eraseTrap_coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    eraseTrap (coreTripleSXP P host Ok) =
      obsTriple Ok (fun s q => CoreObsLXP P host s q.1 q.2) := by
  refine Prod.ext (funext fun s => funext fun q => Set.ext fun ⟨cs, e⟩ => ?_) rfl
  constructor
  · rintro ⟨⟨c, e'⟩, ⟨hq, h⟩, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨hq, ?_⟩
    rcases e' with ⟨r | _, s₂⟩ | _ | _
    · exact .inl h
    · exact .inl ⟨_, h⟩
    · exact h.elim
    · exact .inr ⟨rfl, h⟩
  · rintro ⟨hq, h | ⟨rfl, h⟩⟩
    · rcases e with ⟨r, s₂⟩ | _ | _
      · exact ⟨(cs, .ret (.inl r) s₂), ⟨hq, h⟩, rfl⟩
      · obtain ⟨s₂, h⟩ := h
        exact ⟨(cs, .ret (.inr PUnit.unit) s₂), ⟨hq, h⟩, rfl⟩
      · exact h.elim
    · exact ⟨(cs, .div), ⟨hq, h⟩, rfl⟩

/-- The Core session triple with exceptions has no plain trap. -/
theorem noPlainTrap_coreTripleSXP (P : Numerics.Profile) (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) : NoPlainTrap (coreTripleSXP P host Ok) :=
  fun _ _ _ h => h.2

/-- The native session triple has no plain trap. -/
theorem noPlainTrap_natTripleSXP (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) : NoPlainTrap (natTripleSXP host Ok) :=
  fun s q c h => sessionTripleXP_noPlainTrap s q c h.1.2

/-- **A store-keeping trap of the native session triple** is a store-keeping trap of the session
closure, at a question `Ok` and with a log the host allows. -/
theorem natTripleSXP_trap_iff {host : HostSemantics H} {Ok : Store H → Nat × List Val → Prop}
    {s s₂ : Store H} {q : Nat × List Val} {cs : List (Call (wasmHostSig H))} :
    (cs, .ret (.inr PUnit.unit) s₂) ∈ (natTripleSXP host Ok).1 s q ↔
      Ok s q ∧ (cs, .ret (.inr PUnit.unit) s₂) ∈ wasmEvFunXPS s q ∧
        (coreHostRel host).Consistent cs := by
  constructor
  · rintro ⟨⟨hq, h | ⟨h, -⟩⟩, hc⟩
    · exact ⟨hq, h, hc⟩
    · cases h
  · rintro ⟨hq, h, hc⟩
    exact ⟨⟨hq, .inl h⟩, hc⟩

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **The session square** (deterministic profile). -/
theorem natTripleSXP_eq_coreTripleSXP {o : GrowOracle} {host : HostSemantics H}
    {tags : List TagInst} (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) :
    natTripleSXP host (InvOkXP tags) = coreTripleSXP (profile o) host (InvOkXP tags) := by
  refine eq_of_eraseTrap_eq (noPlainTrap_natTripleSXP _ _) (noPlainTrap_coreTripleSXP _ _ _) ?_
    fun s q cs s₂ => ?_
  · rw [eraseTrap_natTripleSXP, eraseTrap_coreTripleSXP,
      obsTriple_eq_of_square hT hH hE (backDivXP hT hH hE) (backInfXP hT hH hE)]
  · rw [natTripleSXP_trap_iff]
    constructor
    · rintro ⟨hq, h, hc⟩
      exact ⟨hq, (wasmEvFunXPS_trap_iff hT hH hE hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).1 ⟨h, hc⟩⟩
    · rintro ⟨hq, h⟩
      exact ⟨hq, (wasmEvFunXPS_trap_iff hT hH hE hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).2 h⟩

end Silmaril.Proofs.Wasm.Abstract.HostSessionXP

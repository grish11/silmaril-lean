module

public import Silmaril.Games.Abstract.Module.Defs
import Silmaril.Proofs.Games.Abstract.Module.Basic
public import Silmaril.Proofs.Games.Abstract.Module.Congruence

/-!
# Abstract modules: infinite productive runs through recursion

`closeInf` has no infinite runs without internal calls or with a well-founded
call graph, transfers across trap ≈ divergence, and observes a function that
calls an import and then itself: no finite behaviour, no divergence, one
infinite run.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Module

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape Silmaril.Games.Abstract.AFun

universe u

variable {sh : Shape.{u}}

theorem descends_lift_false {c d : sh.ClosedMod} {x y : sh.self.Op} {q : List (Call sh.E)}
    (h : Descends (lift c) d x q y) : False := by
  obtain ⟨_, ⟨w, -, rfl⟩, u, ans, rest, he, -⟩ := h
  have h1 : (⟨.inr y, ans⟩ : Call (sh.E ⊕ₛ sh.self)) ∈ u ++ ⟨.inr y, ans⟩ :: rest :=
    List.mem_append_right _ List.mem_cons_self
  rw [← he] at h1
  obtain ⟨x, -, hx⟩ := List.mem_map.1 h1
  injection hx with h
  cases h

theorem closeInf_lift (c : sh.ClosedMod) (f : sh.F) (s : sh.S) (a : sh.A f) :
    closeInf (lift c) f s a = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, q, -, hd, -, -⟩
  exact descends_lift_false (hd 0)

theorem closeInf_empty_of_wf {R : sh.F → sh.F → Prop} (hR : WellFounded R) {m : sh.OpenMod}
    (hm : RespectsCalls R m) (f : sh.F) (s : sh.S) (a : sh.A f) : closeInf m f s a = ∅ := by
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, q, -, hd, -, -⟩
  have step : ∀ n, R (g (n + 1)).1 (g n).1 := by
    intro n
    obtain ⟨z, hz, u, ans, rest, he, -⟩ := hd n
    exact hm _ _ _ z hz ⟨.inr (g (n + 1)), ans⟩
      (by rw [he]; exact List.mem_append_right _ List.mem_cons_self) (g (n + 1)) rfl
  obtain ⟨n, hn⟩ := @WellFounded.not_rel_apply_succ _ R hR (fun n => (g n).1)
  exact hn (step n)

theorem infChain_transfer {m m' : sh.OpenMod} (h : ORel m m') {x : sh.self.Op}
    {ω : Nat → Call sh.E} (hc : InfChain m (close m) x ω) : InfChain m' (close m') x ω := by
  obtain ⟨g, q, h0, hdesc, hp, hl⟩ := hc
  refine ⟨g, q, h0, fun n => ?_, hp, hl⟩
  obtain ⟨z, hz, u, ans, rest, he, hpre⟩ := hdesc n
  obtain ⟨z', hz', hze⟩ := h _ _ _ z hz
  simp only [obsCollapse, Prod.mk.injEq] at hze
  exact ⟨z', hz', u, ans, rest, hze.1 ▸ he, substPre_transfer (close_crel h) hpre⟩

theorem closeInf_congr {m m' : sh.OpenMod} (h : OpenCollapseEquiv m m') (f : sh.F) (s : sh.S)
    (a : sh.A f) : closeInf m f s a = closeInf m' f s a :=
  Set.ext fun _ => ⟨infChain_transfer (orel_of_equiv h),
    infChain_transfer (orel_of_equiv fun f s a => (h f s a).symm)⟩

/-! ## Example: an import call, then recursion -/

/-- One import, `e : Unit → Unit`; one function, unit state. -/
abbrev shI : Shape.{0} := ⟨⟨PUnit, fun _ => PUnit⟩, PUnit, PUnit, fun _ => PUnit, fun _ => PUnit⟩

/-- The import call. -/
def callE : Call (shI.E ⊕ₛ shI.self) := ⟨.inl ⟨⟩, ⟨⟩⟩

/-- The recursive call. -/
def callSelf : Call (shI.E ⊕ₛ shI.self) := ⟨.inr ⟨⟨⟩, (⟨⟩, ⟨⟩)⟩, (⟨⟩, ⟨⟩)⟩

/-- `f () = e (); f ()`. -/
def m₄ : shI.OpenMod := fun _ _ _ => {([callE, callSelf], .ret ⟨⟩ ⟨⟩)}

theorem close_m₄ : close m₄ = ⊥ := by
  refine le_antisymm (OrderHom.lfp_le _ ?_) bot_le
  rintro f s a y ⟨x, hx, hs⟩
  obtain rfl : x = ([callE, callSelf], .ret ⟨⟩ ⟨⟩) := hx
  cases hs with
  | ext h =>
    cases h with
    | int hc _ => exact hc
    | intTrap hc => exact hc
    | intDiv hc => exact hc

theorem descends_m₄ {c : shI.ClosedMod} {x y : shI.self.Op} {q : List (Call shI.E)}
    (h : Descends m₄ c x q y) : q ≠ [] := by
  obtain ⟨z, hz, u, ans, rest, he, hp⟩ := h
  obtain rfl : z = ([callE, callSelf], .ret ⟨⟩ ⟨⟩) := hz
  rcases u with _ | ⟨u₀, _ | ⟨u₁, u'⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at he
    injection he.1 with h
    cases h
  · cases hp with
    | ext hp' => cases hp'; simp
    | int _ _ => simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
                 injection he.1 with h
                 cases h
  · simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨-, -, he⟩ := he
    simp at he

theorem closeD_m₄ : closeD m₄ ⟨⟩ ⟨⟩ ⟨⟩ = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro (h | ⟨-, g, q, N, -, hd, hq, -⟩)
  · rw [close_m₄] at h; exact h
  · exact descends_m₄ (hd N) (hq N le_rfl)

/-- The stream of import calls `e (), e (), …`. -/
def eStream : Nat → Call shI.E := fun _ => ⟨⟨⟩, ⟨⟩⟩

theorem length_flatMap_single (n : Nat) :
    ((List.range n).flatMap fun _ => ([⟨⟨⟩, ⟨⟩⟩] : List (Call shI.E))).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append]; simp [ih]

theorem eStream_mem : eStream ∈ closeInf m₄ ⟨⟩ ⟨⟩ ⟨⟩ := by
  refine ⟨fun _ => ⟨⟨⟩, (⟨⟩, ⟨⟩)⟩, fun _ => [⟨⟨⟩, ⟨⟩⟩], rfl, fun n => ?_, fun n i _ => ?_,
    fun N => ⟨N, (length_flatMap_single N).ge⟩⟩
  · exact ⟨([callE, callSelf], .ret ⟨⟩ ⟨⟩), rfl, [callE], (⟨⟩, ⟨⟩), [], rfl, .ext .nil⟩
  · simp only [eStream]

end Silmaril.Proofs.Games.Abstract.Module

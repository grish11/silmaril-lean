module

public import Silmaril.Proofs.Wasm.Abstract.Decomp.Bridge

/-!
# The enriched closing against Core 3.0 (proofs)

Native descent paths and chains are `Shape.DescPath` and `Shape.DivChain` of
the open module (`descPath_of_bodyPath`, `bodyPath_of_descPath`,
`divChain_of_chain`). With `callDiv_path_or_chain`, Core divergence of a
typed invocation is a descent path to local divergence or a divergence chain
(`diverges_iff_path_or_chain`). So the Core 3.0 abstract function is the
enriched closing (`wasmFun_eq_closedDL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Decomp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Proofs.Wasm.Abstract.Closing

variable {H : Type}

/-- The call has a typed function. -/
def Typed (x : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), x.2.2.funcs[x.1]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs)

theorem typed_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReach x y) : Typed y := by
  obtain ⟨_, _, _, _, hr⟩ := h
  exact reach_typed hr

theorem descPath_of_bodyPath {x z : (wasmOShape H).self.Op} (h : BodyPath x z) (hx : Typed x) :
    Shape.DescPath wasmOpen (Shape.close wasmOpen) x [] z := by
  induction h with
  | refl => exact .refl _
  | step hxy _ ih =>
    exact Shape.DescPath.step (q := []) ((bodyReach_iff_descends hx).mp hxy) (ih (typed_of_bodyReach hxy))

theorem bodyPath_of_descPath {x z : (wasmOShape H).self.Op} {qs : List (Call Sig.empty)}
    (h : Shape.DescPath wasmOpen (Shape.close wasmOpen) x qs z) : BodyPath x z := by
  induction h with
  | refl => exact .refl _
  | @step x y z q qs hD _ ih =>
    obtain rfl := nil_of_empty q
    have hx : Typed x := by
      obtain ⟨_, ⟨fi, _, ps, rs, _, _, _, _, hfi, _, hty, _⟩, _⟩ := hD
      exact ⟨fi, ps, rs, hfi, hty⟩
    exact .step ((bodyReach_iff_descends hx).mpr hD) ih

theorem divChain_of_chain {x : (wasmOShape H).self.Op} (hx : Typed x)
    {g : Nat → (wasmOShape H).self.Op} (hg : g 0 = x) (h : ∀ n, BodyReach (g n) (g (n + 1))) :
    Shape.DivChain wasmOpen (Shape.close wasmOpen) x [] := by
  have ht : ∀ n, Typed (g n) := fun n => by
    rcases n with _ | n
    · exact hg ▸ hx
    · exact typed_of_bodyReach (h n)
  exact ⟨g, fun _ => [], 0, hg, fun n => (bodyReach_iff_descends (ht n)).mp (h n),
    fun _ _ => rfl, rfl⟩

theorem typed_of_invokeOk {s : Store H} {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    Typed (⟨a, (vs, s)⟩ : (wasmOShape H).self.Op) := by
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := hok
  refine ⟨fi, ps.toList, rs.toList, hfi, ?_⟩
  unfold Validation.DefType.funcType?
  rw [Validation.Expand.iff.mp he]

/-- **Core 3.0 divergence decomposes**: a finite descent path to a call that
diverges within its own function, or an infinite chain of descents. -/
theorem diverges_iff_path_or_chain {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    Diverges P closedHost (invoke s a vs) ↔
      (∃ z, Shape.DescPath wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ [] z ∧ wasmLocalDiv z) ∨
        Shape.DivChain wasmOpen (Shape.close wasmOpen) ⟨a, (vs, s)⟩ [] := by
  rw [Interp.core_diverges_iff_funDiv hs hF hS hok P]
  constructor
  · intro hf
    rcases callDiv_path_or_chain (x := ⟨a, (vs, s)⟩) hf with ⟨z, hp, hl⟩ | ⟨g, hg, hr⟩
    · exact .inl ⟨z, descPath_of_bodyPath hp (typed_of_invokeOk hok), hl⟩
    · exact .inr (divChain_of_chain (typed_of_invokeOk hok) hg hr)
  · rintro (⟨z, hp, hl⟩ | hc)
    · exact callDiv_of_path (bodyPath_of_descPath hp) hl
    · rw [← Interp.core_diverges_iff_funDiv hs hF hS hok P, diverges_iff hs hF hS hok P]
      exact no_closedOutcome_of_divChain hc

/-- **The Core 3.0 abstract function is the enriched closing** of the open
module. -/
theorem wasmFun_eq_closedDL {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs = wasmClosedDL a s vs := by
  have hcl : Shape.close wasmOpen a s vs = ∅ ↔ Diverges P closedHost (invoke s a vs) := by
    rw [diverges_iff hs hF hS hok P, close_wasmOpen, Set.eq_empty_iff_forall_notMem]
    exact ⟨fun h s' fl hc => h _ ⟨s', fl, hc, rfl⟩, fun h _ ⟨s', fl, hc, _⟩ => h s' fl hc⟩
  rw [wasmFun_eq_close hs hF hS hok P]
  ext ⟨q, e⟩
  obtain rfl := nil_of_empty q
  have hd := diverges_iff_path_or_chain hs hF hS hok P
  simp only [wasmClosedDL, Shape.closeDL, Shape.closeD, Set.mem_union, Set.mem_ofPred_eq,
    Prod.mk.injEq, true_and]
  constructor
  · rintro (h | ⟨rfl, hc⟩)
    · exact .inl (.inl h)
    · rcases hd.mp (hcl.mp hc) with hp | hc'
      · exact .inr ⟨rfl, hp⟩
      · exact .inl (.inr ⟨rfl, hc'⟩)
  · rintro ((h | ⟨rfl, hc⟩) | ⟨rfl, hp⟩)
    · exact .inl h
    · exact .inr ⟨rfl, hcl.mpr (hd.mpr (.inr hc))⟩
    · exact .inr ⟨rfl, hcl.mpr (hd.mpr (.inl hp))⟩

end Silmaril.Proofs.Wasm.Abstract.Decomp

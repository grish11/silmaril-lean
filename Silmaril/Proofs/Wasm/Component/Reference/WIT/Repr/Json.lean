module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Json.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms
public import Silmaril.Formats.JsonEvents.Thms
public import Silmaril.Formats.JsonLines.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json

open Silmaril.Formats Silmaril.Wasm.Component.WIT

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource} {K S : Type}
  {tk ts : ValType Ref Resource}

theorem mem_eventLangAt_iff (rk : Repr E K tk) (rs : Repr E S ts) {okK : K → Prop}
    {okS : S → Prop} {d : Nat} {v : (ValType.list (eventType tk ts)).Interp E} :
    v ∈ (Repr.events rk rs).lang (Json.eventLangAt okK okS d) ↔
      ∃ t : JsonEvents.Tree K S, Repr.events rk rs t.toEvents = v ∧
        (∀ e ∈ t.toEvents, Json.ValidEvent okK okS e) ∧ t.depth ≤ d := by
  refine (Repr.mem_lang' (Repr.events rk rs)).trans ?_
  constructor
  · rintro ⟨⟨⟨t, ht⟩, hv⟩, hd⟩
    refine ⟨t, ?_, ht ▸ hv, ?_⟩
    · rw [ht, Equiv.apply_symm_apply]
    · rw [← JsonEvents.toEvents_mem_depthBound_iff, ht]; exact hd
  · rintro ⟨t, rfl, hv, hd⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨⟨⟨t, rfl⟩, hv⟩, (JsonEvents.toEvents_mem_depthBound_iff t d).2 hd⟩

/-- Lines without `0A`, each terminated by `0A`, determine the lines. -/
theorem terminated_injOn {ls ls' : List (List UInt8)} (h : ∀ l ∈ ls, JsonLines.lf ∉ l)
    (h' : ∀ l ∈ ls', JsonLines.lf ∉ l)
    (he : JsonLines.terminated ls = JsonLines.terminated ls') : ls = ls' := by
  rw [JsonLines.terminated_eq_frameItems, JsonLines.terminated_eq_frameItems] at he
  induction ls generalizing ls' with
  | nil =>
    cases ls' with
    | nil => rfl
    | cons b bs => simp [Silmaril.Streams.frameItems] at he
  | cons a as ih =>
    cases ls' with
    | nil => simp [Silmaril.Streams.frameItems] at he
    | cons b bs =>
      simp only [Silmaril.Streams.frameItems, List.flatMap_cons, List.append_assoc,
        List.singleton_append] at he
      have key : ∀ (a b : List UInt8) (x y : List UInt8), JsonLines.lf ∉ a → JsonLines.lf ∉ b →
          a ++ JsonLines.lf :: x = b ++ JsonLines.lf :: y → a = b ∧ x = y := by
        intro a
        induction a with
        | nil =>
          intro b x y _ hb hxy
          cases b with
          | nil => simpa using hxy
          | cons c cs =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at hxy
            exact absurd (hxy.1 ▸ List.mem_cons_self) hb
        | cons c cs ih =>
          intro b x y ha hb hxy
          cases b with
          | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at hxy
            exact absurd (hxy.1 ▸ List.mem_cons_self) ha
          | cons c' cs' =>
            simp only [List.cons_append, List.cons.injEq] at hxy
            obtain ⟨rfl, hxy⟩ := hxy
            obtain ⟨rfl, rfl⟩ := ih cs' x y (fun hm => ha (List.mem_cons_of_mem _ hm))
              (fun hm => hb (List.mem_cons_of_mem _ hm)) hxy
            exact ⟨rfl, rfl⟩
      obtain ⟨rfl, hr⟩ := key a b _ _ (h a List.mem_cons_self) (h' b List.mem_cons_self) he
      rw [ih (fun l hl => h l (List.mem_cons_of_mem _ hl))
        (fun l hl => h' l (List.mem_cons_of_mem _ hl)) hr]

end Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json

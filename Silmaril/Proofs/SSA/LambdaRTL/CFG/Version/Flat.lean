module

public import Silmaril.SSA.LambdaRTL.CFG.Version.Flat.Defs
public import Silmaril.SSA.LambdaRTL.Version.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.FlatVersion

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v}

private theorem term_roundtrip (term : Term V K F) :
    Term.ofRegion? term.toRegion = some term := by
  induction term with
  | br => rfl
  | case _ _ _ _ _ ihLeft ihRight =>
    simp [Term.ofRegion?, Term.toRegion, ihLeft, ihRight]

private theorem body_roundtrip (body : Body V K F) :
    Body.ofRegion? body.toRegion = some body := by
  induction body with
  | term term =>
    have parsed := term_roundtrip term
    cases term with
    | br => rfl
    | case =>
      rw [Term.toRegion] at parsed
      simp [Body.ofRegion?, Body.toRegion, Term.toRegion, parsed]
  | let1 _ _ _ ih => simp [Body.ofRegion?, Body.toRegion, ih]
  | let2 _ _ _ _ ih => simp [Body.ofRegion?, Body.toRegion, ih]

private theorem collect_joinAll (entry : Region V K F)
    (blocks suffix : List (K × Block V K F)) :
    ofRegion?.collect (joinAll entry blocks) suffix =
      ofRegion?.collect entry (blocks ++ suffix) := by
  induction blocks generalizing entry suffix with
  | nil => rfl
  | cons block blocks ih =>
    rw [joinAll, ih]
    simp [ofRegion?.collect, body_roundtrip]

theorem ofRegion?_toRegion (graph : CFG V K F) : ofRegion? graph.toRegion = some graph := by
  rw [ofRegion?, CFG.toRegion, collect_joinAll, List.append_nil]
  cases graph with
  | mk entry blocks =>
    have parsed := body_roundtrip entry
    cases entry with
    | let1 | let2 =>
      simp only [Body.toRegion] at parsed ⊢
      simp [ofRegion?.collect, parsed]
    | term term =>
      cases term <;> simp only [Body.toRegion, Term.toRegion] at parsed ⊢
      all_goals simp [ofRegion?.collect, parsed]

private theorem joinAll_append (entry : Region V K F) (blocks tail : List (K × Block V K F)) :
    joinAll entry (blocks ++ tail) = joinAll (joinAll entry blocks) tail := by
  induction blocks generalizing entry with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem term_readback (region : Region V K F) {term : Term V K F}
    (parsed : Term.ofRegion? region = some term) : term.toRegion = region := by
  induction region generalizing term with
  | br => cases parsed; rfl
  | case op x left y right ihLeft ihRight =>
    simp only [Term.ofRegion?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
    obtain ⟨left', hLeft, right', hRight, rfl⟩ := parsed
    simp [Term.toRegion, ihLeft hLeft, ihRight hRight]
  | let1 | let2 | join => simp [Term.ofRegion?] at parsed

private theorem body_readback (region : Region V K F) {body : Body V K F}
    (parsed : Body.ofRegion? region = some body) : body.toRegion = region := by
  induction region generalizing body with
  | br => cases parsed; rfl
  | let1 _ _ _ ih | let2 _ _ _ _ ih =>
    simp only [Body.ofRegion?, Option.map_eq_some_iff] at parsed
    obtain ⟨body', hBody, rfl⟩ := parsed
    simp [Body.toRegion, ih hBody]
  | case =>
    simp only [Body.ofRegion?, Option.map_eq_some_iff] at parsed
    obtain ⟨term, hTerm, rfl⟩ := parsed
    exact term_readback _ hTerm
  | join => simp [Body.ofRegion?, Term.ofRegion?] at parsed

private theorem collect_readback (region : Region V K F)
    (suffix : List (K × Block V K F)) {graph : CFG V K F}
    (parsed : ofRegion?.collect region suffix = some graph) :
    graph.toRegion = joinAll region suffix := by
  induction region generalizing suffix with
  | join earlier label param handler ih _ =>
    rw [ofRegion?.collect] at parsed
    obtain ⟨body, hBody, hGraph⟩ := Option.bind_eq_some_iff.mp parsed
    simpa only [joinAll, body_readback _ hBody] using ih _ hGraph
  | _ =>
    rw [ofRegion?.collect] at parsed
    obtain ⟨body, hBody, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact congrArg (fun r => joinAll r suffix) (body_readback _ hBody)

theorem ofRegion?_eq_some_iff (region : Region V K F) (graph : CFG V K F) :
    ofRegion? region = some graph ↔ graph.toRegion = region :=
  ⟨collect_readback region [], fun eq => eq ▸ ofRegion?_toRegion graph⟩

open Version

private theorem unpack_body (regs : List V) (src : V × Nat) (depth : Nat)
    (body : Body (V × Nat) K F) :
    ∃ target : Body (V × Nat) K F, target.toRegion = unpack regs src depth body.toRegion := by
  induction regs generalizing src depth with
  | nil => exact ⟨body, rfl⟩
  | cons reg regs ih =>
    obtain ⟨target, ht⟩ := ih (reg, depth + 2) (depth + 2)
    exact ⟨.let2 (reg, depth + 1) (reg, depth + 2) (.val (.var src)) target, by
      simp [Body.toRegion, unpack, ht]⟩

section Version

variable [DecidableEq V] [DecidableEq K]

private theorem term_version (term : Term V K F)
    (labels : K → Option (List V)) (live : List V) (current : V → Nat) (depth : Nat) :
    ∃ target : Term (V × Nat) K F, target.toRegion = version labels live current depth term.toRegion := by
  induction term generalizing current depth with
  | br label arg =>
    cases h : labels label with
    | none => exact ⟨.br label (rn current arg), by simp [Term.toRegion, version, h]⟩
    | some vars =>
      exact ⟨.br label (.pair (rn current arg) (pack current vars)), by
        simp [Term.toRegion, version, h]⟩
  | case op x left y right ihLeft ihRight =>
    obtain ⟨left', hLeft⟩ := ihLeft (setv current x (depth + 1)) (depth + 1)
    obtain ⟨right', hRight⟩ := ihRight (setv current y (depth + 1)) (depth + 1)
    exact ⟨.case (rnOp current op) (x, depth + 1) left' (y, depth + 1) right', by
      simp [Term.toRegion, version, hLeft, hRight]⟩

private theorem body_version (body : Body V K F)
    (labels : K → Option (List V)) (live : List V) (current : V → Nat) (depth : Nat) :
    ∃ target : Body (V × Nat) K F, target.toRegion = version labels live current depth body.toRegion := by
  induction body generalizing current depth with
  | term term =>
    obtain ⟨target, ht⟩ := term_version term labels live current depth
    exact ⟨.term target, ht⟩
  | let1 x op body ih =>
    obtain ⟨target, ht⟩ := ih (setv current x (depth + 1)) (depth + 1)
    exact ⟨.let1 (x, depth + 1) (rnOp current op) target, by
      simp [Body.toRegion, version, ht]⟩
  | let2 x y op body ih =>
    obtain ⟨target, ht⟩ := ih (setv (setv current x (depth + 1)) y (depth + 2)) (depth + 2)
    exact ⟨.let2 (x, depth + 1) (y, depth + 2) (rnOp current op) target, by
      simp [Body.toRegion, version, ht]⟩

private theorem version_representable (entry : Body V K F) (blocks : List (K × Block V K F))
    (labels : K → Option (List V)) (live : List V) (current : V → Nat) (depth : Nat) :
    ∃ target : CFG (V × Nat) K F,
      target.toRegion = version labels live current depth (joinAll entry.toRegion blocks) ∧
      target.blocks.map Prod.fst = blocks.map Prod.fst := by
  induction blocks using List.reverseRecOn generalizing labels live with
  | nil =>
    obtain ⟨body, hb⟩ := body_version entry labels live current depth
    exact ⟨⟨body, []⟩, hb, rfl⟩
  | append_singleton blocks block ih =>
    let regs := liveIns block.2.body.toRegion block.2.param live
    obtain ⟨earlier, hp, hLabels⟩ :=
      ih (setl labels block.1 regs) (regs ++ live).dedup
    obtain ⟨body, hb⟩ := body_version block.2.body labels live
      (unpackCur regs (setv current block.2.param (depth + 2)) (depth + 3))
      (depth + 3 + 2 * regs.length)
    obtain ⟨unpacked, hu⟩ := unpack_body regs (block.2.param, depth + 3) (depth + 3) body
    let param := (block.2.param, depth + 1)
    let handler := Body.let2 (block.2.param, depth + 2) (block.2.param, depth + 3)
      (.val (.var param)) unpacked
    refine ⟨⟨earlier.entry, earlier.blocks ++ [(block.1, ⟨param, handler⟩)]⟩, ?_, ?_⟩
    · change joinAll earlier.entry.toRegion (earlier.blocks ++ _) = _
      simp only [joinAll_append, joinAll]
      change Region.join earlier.toRegion _ _ _ = _
      simp only [version, hp, handler, Body.toRegion, hu, hb, param, regs]
    · simp [hLabels]

theorem version_reifies (source : CFG V K F) :
    ∃ target : CFG (V × Nat) K F,
      ofRegion? (versionTop source.toRegion) = some target ∧
      target.blocks.map Prod.fst = source.blocks.map Prod.fst := by
  obtain ⟨target, hRegion, hLabels⟩ :=
    version_representable source.entry source.blocks (fun _ => none) [] (fun _ => 0) 0
  change target.toRegion = versionTop source.toRegion at hRegion
  exact ⟨target, hRegion ▸ ofRegion?_toRegion target, hLabels⟩

end Version
end Silmaril.Proofs.SSA.LambdaRTL.CFG.FlatVersion

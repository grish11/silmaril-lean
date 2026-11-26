module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Version.Flat
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Lexical
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness
import Silmaril.Proofs.SSA.LambdaRTL.Version

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K]

private theorem versionBody_readback (body : Body V K F) (labels : K → Option (List V))
    (live : List V) (current : V → Nat) (depth : Nat) :
    (versionBody body labels live current depth).toRegion =
      Version.version labels live current depth body.toRegion :=
  FlatVersion.body_readback _ (Option.some_get _).symm

omit [DecidableEq V] [DecidableEq K] in
private theorem unpackBody_readback (regs : List V) (src : V × Nat) (depth : Nat)
    (body : Body (V × Nat) K F) :
    (unpackBody regs src depth body).toRegion = Version.unpack regs src depth body.toRegion :=
  FlatVersion.body_readback _ (Option.some_get _).symm

omit [DecidableEq K] in
private theorem registers_entry (graph : CFG V K F) (reg : V)
    (free : reg ∈ graph.entry.toRegion.fvList) : reg ∈ registers graph := by
  simp [registers, free]

omit [DecidableEq K] in
private theorem registers_block (graph : CFG V K F) (item : K × Block V K F)
    (member : item ∈ graph.blocks) (reg : V) (free : reg ∈ item.2.body.toRegion.fvList) :
    reg ∈ registers graph := by
  simp only [registers, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨item, member, free⟩

private theorem destinations_supported (graph : CFG V K F) (label : K) (regs : List V)
    (layout : destinations graph label = some regs) (reg : V) (member : reg ∈ regs) :
    reg ∈ registers graph := by
  cases found : graph.blocks.lookup label with
  | none => simp [destinations, found] at layout
  | some block =>
    simp [destinations, found] at layout
    subst regs
    exact (List.mem_filter.mp member).1

omit [DecidableEq V] in
private theorem lookup_member (table : List (K × Block V K F)) (label : K) (block : Block V K F)
    (found : table.lookup label = some block) : (label, block) ∈ table := by
  induction table with
  | nil => simp at found
  | cons item rest ih =>
    rcases item with ⟨key, body⟩
    cases same : label == key with
    | false =>
      rw [List.lookup_cons, same] at found
      exact List.mem_cons_of_mem _ (ih found)
    | true =>
      have equal : label = key := beq_iff_eq.mp same
      subst key
      simp at found
      subst body
      exact List.mem_cons_self

private theorem lookup_compile (graph : CFG V K F) (label : K) :
    (compile graph).blocks.lookup label = (graph.blocks.lookup label).map (compileBlock graph) := by
  change (graph.blocks.map (fun item => (item.1, compileBlock graph item.2))).lookup label = _
  generalize graph.blocks = table
  induction table with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all

theorem compile_entry_isSSA (graph : CFG V K F) :
    (compile graph).entry.toRegion.IsSSA ((registers graph).map fun reg => (reg, 0)).toFinset := by
  change (versionBody graph.entry _ _ _ _).toRegion.IsSSA _
  rw [versionBody_readback]
  apply Silmaril.SSA.LambdaRTL.Version.version_isSSA _ _ _ _ _ _ (destinations_supported graph)
  · intro name member
    simp only [List.mem_toFinset, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    exact Nat.le_refl _
  · intro reg member
    have supported := member.elim (registers_entry graph reg) id
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨reg, supported, rfl⟩)

private theorem compileBlock_isSSA (graph : CFG V K F) (item : K × Block V K F)
    (member : item ∈ graph.blocks) :
    (compileBlock graph item.2).body.toRegion.IsSSA {(compileBlock graph item.2).param} := by
  let block := item.2
  let ctx : Finset (V × Nat) := insert (block.param, 2)
    (insert (block.param, 1) {(block.param, 0)})
  have bounded : ∀ p ∈ ctx, p.2 ≤ 2 := by
    intro p hp
    simp only [ctx, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  simp only [compileBlock, Body.toRegion, Region.IsSSA, Op.fv, Val.fv]
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  rw [unpackBody_readback, versionBody_readback]
  change (Silmaril.SSA.LambdaRTL.Version.unpack (slots graph block) (block.param, 2) 2 _).IsSSA ctx
  apply Version.unpack_isSSA _ _ _ _ _ (by simp [ctx]) bounded
  apply Silmaril.SSA.LambdaRTL.Version.version_isSSA _ _ _ _ _ _ (destinations_supported graph)
    (Version.unpackCtx_bound _ _ _ bounded)
  intro reg read
  by_cases same : reg = block.param
  · subst reg
    have absent : block.param ∉ slots graph block := by simp [slots]
    rw [blockVersions, Version.unpackCur_of_not_mem _ _ _ _ absent, Version.setv_self]
    exact Version.subset_unpackCtx _ _ ctx (by simp [ctx])
  · have supported : reg ∈ registers graph := read.elim (registers_block graph item member reg) id
    exact Version.unpackCur_mem _ _ _ _ _ (by simp [slots, supported, same])

theorem compile_blocks_areSSA (graph : CFG V K F) (item : K × Block (V × Nat) K F)
    (member : item ∈ (compile graph).blocks) : item.2.body.toRegion.IsSSA {item.2.param} := by
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  exact compileBlock_isSSA graph source present

variable [Monad M] [LawfulMonad M]

theorem entry_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    encode model graph <$> enter model graph (fun reg => input (reg, 0)) =
      (compile graph).entry.evalJump model input := by
  rw [body_evalJump]
  change _ = (versionBody graph.entry (destinations graph) (registers graph) _ _).toRegion.evalSSA
    model input
  rw [versionBody_readback, Version.version_evalSSA model pairs _ _ _ _ _ _ _
    (destinations_supported graph) (fun _ _ => rfl)]
  simp [enter, Body.exec_eq]
  rfl

private theorem block_evalJump (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG V K F) (label : K) (block : Block V K F) (member : (label, block) ∈ graph.blocks)
    (payload : α) (store : V → α) (input : V × Nat → α) :
    (compileBlock graph block).body.evalJump model
      (upd input (compileBlock graph block).param
        (model.pair payload (Version.packVal model store (slots graph block)))) =
      block.body.exec model (fun k a next => pure (encode model graph (k, a, next)))
        (upd store block.param payload) := by
  rw [body_evalJump, Body.exec_eq]
  simp only [compileBlock, Body.toRegion, unpackBody_readback, versionBody_readback,
    Region.evalSSA, Op.eval, Val.eval]
  rw [show upd input (block.param, 0)
      (model.pair payload (Version.packVal model store (slots graph block))) (block.param, 0) =
        model.pair payload (Version.packVal model store (slots graph block)) from by simp [upd]]
  simp only [pure_bind, pairs.unpair_pair]
  rw [Version.unpack_evalSSA model pairs store _ _ _ _ _ (by simp [upd])]
  apply Version.version_evalSSA model pairs
  · exact destinations_supported graph
  · intro reg read
    by_cases same : reg = block.param
    · subst reg
      have absent : block.param ∉ slots graph block := by simp [slots]
      rw [blockVersions, Version.unpackCur_of_not_mem _ _ _ _ absent,
        Version.unpackEnv_frame model store _ _ _ _ absent]
      simp [Version.setv, upd]
    · have supported : reg ∈ registers graph := read.elim
        (registers_block graph (label, block) member reg) id
      have packed : reg ∈ slots graph block := by simp [slots, supported, same]
      rw [blockVersions, Version.unpackEnv_mem model store _ _ _ _ _ packed]
      simp [upd, same]

theorem step_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) (transfer : Transfer V K α) :
    Sum.map obs (encode model graph) <$> step model graph.blocks transfer =
      Cyclic.stepSSA model (compile graph).blocks input (encode model graph transfer) := by
  rcases transfer with ⟨label, payload, store⟩
  have key : (encode model graph (label, payload, store)).1 = label := Version.enc_fst _ _ _
  cases found : graph.blocks.lookup label with
  | none => simp [step, Cyclic.stepSSA, lookup_compile, found, encode, Version.enc, destinations, obs]
  | some block =>
    have packet : (encode model graph (label, payload, store)).2 =
        model.pair payload (Version.packVal model store (slots graph block)) := by
      simp [encode, Version.enc, destinations, found]
    simp only [step, Cyclic.stepSSA, key, lookup_compile, found, Option.map_some]
    rw [packet, block_evalJump model pairs graph label block (lookup_member _ _ _ found)]
    simp only [← Body.exec_map, map_pure, Sum.map_inr]

variable [Iterate M] [LawfulElgotMonad M]

theorem run_commutes (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    (input : V × Nat → α) :
    obs <$> Cyclic.run model graph (fun reg => input (reg, 0)) =
      Cyclic.runSSA model (compile graph) input := by
  have run_entry : Cyclic.run model graph (fun reg => input (reg, 0)) =
      enter model graph (fun reg => input (reg, 0)) >>= iter (step model graph.blocks) := by
    simp [Cyclic.run, enter, Body.exec_eq]
  rw [run_entry, Cyclic.runSSA, ← entry_commutes model pairs]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro transfer
  exact iter_obs_of_step_encoding model graph.blocks (encode model graph) _
    (step_commutes model pairs graph input) transfer

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicVersion

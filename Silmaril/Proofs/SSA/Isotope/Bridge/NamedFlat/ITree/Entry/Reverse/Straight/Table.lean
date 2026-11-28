module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Body
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

private theorem term_readback {V K : Type u} {F : Type v} (tail : CFG.Term V K F) :
    CFG.Term.ofRegion? tail.toRegion = some tail := by
  induction tail <;> simp [CFG.Term.ofRegion?, CFG.Term.toRegion, *]

private theorem body_readback {V K : Type u} {F : Type v} (src : CFG.Body V K F) :
    CFG.Body.ofRegion? src.toRegion = some src := by
  induction src with
  | let1 | let2 => simp [CFG.Body.ofRegion?, CFG.Body.toRegion, *]
  | term tail => cases tail <;> simp [CFG.Body.toRegion, CFG.Body.ofRegion?, CFG.Term.toRegion,
      CFG.Term.ofRegion?, term_readback]

private theorem unpack_empty {V K : Type u} {F : Type v} (src : V × Nat) (d : Nat)
    (body : CFG.Body (V × Nat) K F) : Versioning.unpackBody [] src d body = body :=
  Option.get_of_eq_some _ (body_readback body)

private theorem unpack_cons {V K : Type u} {F : Type v} (reg : V) (rest : List V)
    (src : V × Nat) (d : Nat) (body : CFG.Body (V × Nat) K F) :
    Versioning.unpackBody (reg :: rest) src d body =
      .let2 (reg, d + 1) (reg, d + 2) (.val (.var src))
        (Versioning.unpackBody rest (reg, d + 2) (d + 2) body) := by
  have read : CFG.Body.ofRegion? (Version.unpack rest (reg, d + 2) (d + 2) body.toRegion) =
      some (Versioning.unpackBody rest (reg, d + 2) (d + 2) body) := (Option.some_get _).symm
  exact Option.get_of_eq_some _ (by simp [Version.unpack, CFG.Body.ofRegion?, read])

private theorem lookup_index {K : Type u} {A : Type v} [BEq K] (items : List (K × A)) (label : K) :
    items.lookup label = (items.findFinIdx? (fun item => label == item.1)).map
      (fun i => items[i].2) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, entry⟩
    simp only [List.lookup_cons, List.findFinIdx?_cons]
    cases label == key <;> simp [ih, Function.comp_def]

variable {Base V K : Type u} {F : Type v} [DecidableEq V] [DecidableEq K]

private abbrev mappedRows (graph : CFG V K F) (build : CFG.Block V K F → CFG.Block (V × Nat) K F) :=
  graph.blocks.map fun item => (item.1, build item.2)

omit [DecidableEq V] in
private theorem routes_saved (graph : CFG V K F) (exits : List K)
    (layout : CFG.Block V K F → List V) (build : CFG.Block V K F → CFG.Block (V × Nat) K F)
    (captures : Fin (mappedRows graph build).length → List (V × Ty Base))
    (required : K → List (V × Ty Base))
    (R : Fin (mappedRows graph build).length → Ty Base) (D : Fin exits.length → Ty Base)
    (slots : ∀ i : Fin graph.blocks.length, layout graph.blocks[i].2 =
      (captures (Fin.cast (List.length_map _).symm i)).map Prod.fst)
    (selected : ∀ k i, (mappedRows graph build).findFinIdx? (fun item => k == item.1) = some i →
      required k = captures i) :
    Routes (labelIndex (mappedRows graph build) exits) (Versioning.destinationsWith graph layout)
      required (SSA.FiniteSum.append R D)
      (SSA.FiniteSum.append (fun i => .product (R i) (LiveOut.recordType (captures i))) D) := by
  intro label i numbered
  let compiled := mappedRows graph build
  have order : (compiled.findFinIdx? (fun item => label == item.1)).map Fin.val =
      (graph.blocks.findFinIdx? (fun item => label == item.1)).map Fin.val := by
    simp [← List.findIdx?_eq_map_findFinIdx?_val, compiled, mappedRows, Function.comp_def]
  change labelIndex compiled exits label = some i at numbered
  cases hCompiled : compiled.findFinIdx? (fun item => label == item.1) with
  | none =>
    cases hSource : graph.blocks.findFinIdx? (fun item => label == item.1) with
    | some j => simp [hCompiled, hSource] at order
    | none =>
      simp only [labelIndex, hCompiled, Option.map_eq_some_iff] at numbered
      obtain ⟨j, _, rfl⟩ := numbered
      refine Or.inl ⟨?_, ?_⟩
      · rw [Versioning.destinationsWith, lookup_index, hSource]
        rfl
      · rw [SSA.FiniteSum.append_right, SSA.FiniteSum.append_right]
  | some k =>
    cases hSource : graph.blocks.findFinIdx? (fun item => label == item.1) with
    | none => simp [hCompiled, hSource] at order
    | some j =>
      simp only [labelIndex, hCompiled, Option.some.injEq] at numbered
      subst i
      have row : Fin.cast (List.length_map _).symm j = k :=
        Fin.ext (by simpa [hCompiled, hSource] using order.symm)
      have fields := selected label k hCompiled
      refine Or.inr ⟨?_, ?_⟩
      · rw [Versioning.destinationsWith, lookup_index, hSource, fields]
        exact congrArg some ((slots j).trans (congrArg (fun i => (captures i).map Prod.fst) row))
      · rw [SSA.FiniteSum.append_left, SSA.FiniteSum.append_left, fields]

private theorem tabulate_checked {A : Type u} {count : Nat}
    {f : Fin count → Option A} {p : Fin count → A → Prop}
    (each : ∀ i, ∃ out, f i = some out ∧ p i out) :
    ∃ table, tabulate count f = some table ∧ ∀ i, p i (table i) := by
  induction count with
  | zero => exact ⟨Fin.elim0, rfl, fun i => i.elim0⟩
  | succ count ih =>
    obtain ⟨first, hFirst, pFirst⟩ := each 0
    obtain ⟨tail, hTail, pTail⟩ := ih (fun i => each i.succ)
    exact ⟨Fin.cases first tail, by simp [tabulate, hFirst, hTail],
      fun i => Fin.cases pFirst pTail i⟩

omit [DecidableEq K] in
private theorem checked_source [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} {index : K → Option (Fin labels)} {types : Fin labels → Ty Base}
    {names : Names V n} {ctx : BoundCtx (Ty Base) n} {src : CFG.Body V K F}
    (checks : sourceCheck index types names ctx src = true) :
    ∃ flat, body index names src = some flat ∧ checkBody types ctx flat = true := by
  cases found : body index names src <;> simp_all [sourceCheck]

omit [DecidableEq K] in
private theorem entry_scope {n : Nat} (captures : Fin n → V) (ctx : BoundCtx (Ty Base) n) :
    Scope (fun _ => 0) (first captures) ctx (first (fun i => (captures i, 0))) ctx := by
  intro reg i found
  exact ⟨i, by simpa [first] using found, rfl⟩

omit [DecidableEq K] in
private theorem read_pair [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} {index : K → Option (Fin labels)} {types : Fin labels → Ty Base}
    {names : Names (V × Nat) n} {ctx : BoundCtx (Ty Base) n} {packet x y : V × Nat}
    {i : Fin n} {A B : Ty Base} {tail : CFG.Body (V × Nat) K F} {inner : Flat F labels (n + 2)}
    (src : names packet = some i) (type : ctx.get i = .product A B)
    (read : body index (bindName (bindName names x) y) tail = some inner)
    (checked : checkBody types (.snoc (.snoc ctx A) B) inner = true) :
    body index names (.let2 x y (.val (.var packet)) tail) = some (.let₂ (.bv i) inner) ∧
      checkBody types ctx (.let₂ (.bv i) inner) = true :=
  ⟨by simp [body, operand, value, src, read], by simp [checkBody, infer, type, checked]⟩

omit [DecidableEq K] in
/-- Type the actual tuple decoder. At each prefix, track the already
decoded fields at their current versions and the remaining tuple at its
named temporary. The continuation can use every decoded field. -/
private theorem unpack_checked [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (index : K → Option (Fin labels)) (types : Fin labels → Ty Base)
    (remaining known : List (V × Ty Base))
    (distinct : ((remaining.reverse ++ known).map Prod.fst).Nodup)
    (cur : V → Nat) (d : Nat)
    (names : Names (V × Nat) n) (ctx : BoundCtx (Ty Base) n) (packet : V × Nat)
    (i : Fin n) (hit : names packet = some i) (type : ctx.get i = LiveOut.recordType remaining)
    (scope : SavedScope cur known names ctx) (tail : CFG.Body (V × Nat) K F)
    (inside : ∀ {m} (target : Names (V × Nat) m) (typed : BoundCtx (Ty Base) m),
      SavedScope (Version.unpackCur (remaining.map Prod.fst) cur d)
        (remaining.reverse ++ known) target typed →
      ∃ flat, body index target tail = some flat ∧ checkBody types typed flat = true) :
    ∃ flat, body index names (Versioning.unpackBody (remaining.map Prod.fst) packet d tail) = some flat ∧
      checkBody types ctx flat = true := by
  induction remaining generalizing known n cur d packet with
  | nil => simpa [unpack_empty, Version.unpackCur] using inside names ctx scope
  | cons field rest ih =>
    obtain ⟨reg, A⟩ := field
    let next := Version.setv cur reg (d + 1)
    let target := bindName (bindName names (reg, d + 1)) (reg, d + 2)
    let typed := (ctx.snoc A).snoc (LiveOut.recordType rest)
    have distinctNext : ((rest.reverse ++ (reg, A) :: known).map Prod.fst).Nodup := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using distinct
    have knownDistinct : (reg :: known.map Prod.fst).Nodup :=
      (List.nodup_append.mp (by simpa only [List.map_append, List.map_cons] using distinctNext)).2.1
    have fresh := (List.nodup_cons.mp knownDistinct).1
    have nextScope : SavedScope next ((reg, A) :: known) target typed := by
      intro r T mem
      rcases List.mem_cons.mp mem with eq | old
      · cases eq
        exact ⟨(0 : Fin (n + 1)).succ, by simp [next, target, Version.setv, bindName], rfl⟩
      · have ne : r ≠ reg := fun eq => fresh (List.mem_map.mpr ⟨(r, T), old, eq⟩)
        obtain ⟨j, read, ty⟩ := scope r T old
        exact ⟨j.succ.succ, by simp [next, target, Version.setv, bindName, ne, read], ty⟩
    obtain ⟨flat, read, checked⟩ := ih ((reg, A) :: known) distinctNext next (d + 2)
      target typed (reg, d + 2) 0 (by simp [target, bindName]) rfl nextScope
      (fun {_} out outCtx inScope => inside out outCtx (by
        simpa only [List.map_cons, Version.unpackCur, List.reverse_cons, List.append_assoc,
          List.singleton_append] using inScope))
    have result := read_pair (packet := packet) (i := i) (x := (reg, d + 1)) (y := (reg, d + 2))
      (show names packet = some i from hit) (show ctx.get i = .product A (LiveOut.recordType rest) from type)
      read checked
    exact ⟨_, by simpa only [List.map_cons, unpack_cons] using result.1, result.2⟩

private theorem block_checkedWith [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (labelsOf : K → Option (List V)) (live : List V) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (required : K → List (V × Ty Base)) (captures : List (V × Ty Base))
    (routes : Routes index labelsOf required old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (distinct : ((captures.reverse ++ [(src.param, A)]).map Prod.fst).Nodup)
    (keeps : KeepsCapture captures src.body.toRegion)
    (supplies : Supplies required captures src.body.targets)
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlockWith labelsOf live (captures.map Prod.fst) src).param)
      (Versioning.compileBlockWith labelsOf live (captures.map Prod.fst) src).body = some flat ∧
      checkBody new (.snoc ctx (.product A (LiveOut.recordType captures))) flat = true := by
  let p := src.param
  let initial := blockNames (n := n) (p, 0)
  let afterArg := bindName (bindName initial (p, 1)) (p, 2)
  let ctx0 := ctx.snoc (.product A (LiveOut.recordType captures))
  let ctx1 := (ctx0.snoc A).snoc (LiveOut.recordType captures)
  let cur := Version.setv (fun _ => 0) p 1
  let versions := Version.unpackCur (captures.map Prod.fst) cur 2
  let inner := Versioning.versionBody src.body labelsOf live
    versions (2 + 2 * captures.length)
  have arg : SavedScope cur [(p, A)] afterArg ctx1 := by
    intro reg T mem
    have eq : (reg, T) = (p, A) := by simpa using mem
    cases eq
    exact ⟨(0 : Fin (n + 2)).succ, by simp [cur, afterArg, Version.setv, bindName], rfl⟩
  obtain ⟨_, source, typed⟩ := checked_source checked
  obtain ⟨decoded, hDecoded, tDecoded⟩ := unpack_checked index new captures [(p, A)] distinct
    cur 2
    afterArg ctx1 (p, 2) 0 (by simp [afterArg, bindName]) rfl arg inner (by
      intro m names types all
      have scope : Scope versions (blockNames p) (.snoc ctx A) names types := by
        intro r i hit
        by_cases same : r = p
        · subst r
          have eq : i = 0 := by simpa [blockNames, bindName] using hit.symm
          subst i
          exact all p A (by simp)
        · simp [blockNames, bindName, same] at hit
      have saved : SavedScope versions captures names types :=
        fun r T mem => all r T (by simp [mem])
      exact version_body index labelsOf required captures old new routes live src.body
        (2 + 2 * captures.length) versions _ _ names types scope saved keeps supplies source typed)
  have packet : initial (p, 0) = some 0 := by simp [initial, blockNames, bindName]
  obtain ⟨hPacket, tPacket⟩ := read_pair (packet := (p, 0)) (names := initial) (i := 0)
    (ctx := ctx0) (x := (p, 1)) (y := (p, 2)) packet
    (show ctx0.get 0 = .product A (LiveOut.recordType captures) from rfl) hDecoded tDecoded
  refine ⟨_, ?_, tPacket⟩
  simpa only [Versioning.compileBlockWith, List.length_map] using hPacket

private theorem block_checked [DecidableEq Base] [HasTy F (Ty Base)]
    {n labels : Nat} (graph : CFG V K F) (src : CFG.Block V K F)
    (index : K → Option (Fin labels)) (old new : Fin labels → Ty Base)
    (required : K → List (V × Ty Base)) (captures : List (V × Ty Base))
    (routes : Routes index (Versioning.destinations graph) required old new)
    (ctx : BoundCtx (Ty Base) n) (A : Ty Base)
    (slots : Versioning.slots graph src = captures.map Prod.fst)
    (keeps : KeepsCapture captures src.body.toRegion)
    (supplies : Supplies required captures src.body.targets)
    (checked : sourceCheck index old (blockNames src.param) (.snoc ctx A) src.body = true) :
    ∃ flat, body index (blockNames (Versioning.compileBlock graph src).param)
      (Versioning.compileBlock graph src).body = some flat ∧
      checkBody new (.snoc ctx (.product A (LiveOut.recordType captures))) flat = true := by
  have distinct : ((captures.reverse ++ [(src.param, A)]).map Prod.fst).Nodup := by
    rw [List.map_append, List.map_reverse, ← slots, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr (List.Nodup.filter _ (List.nodup_dedup _)), by simp, ?_⟩
    intro reg mem other selected
    have ne := of_decide_eq_true ((List.mem_filter.mp (List.mem_reverse.mp mem)).2)
    have eq : other = src.param := by simpa using selected
    exact eq ▸ ne
  simpa only [Versioning.compileBlock, slots] using
    (block_checkedWith (Versioning.destinations graph) (Versioning.registers graph) src index old new
      required captures routes ctx A distinct keeps supplies checked)

section PacketLocal

variable {n : Nat} [DecidableEq Base] [HasTy F (Ty Base)]

set_option maxHeartbeats 400000 in
theorem packetLocalSource_sound (graph : CFG V K F) (names : Fin n → V)
    (ctx : BoundCtx (Ty Base) n) (exits : List K) (external : Fin exits.length → Ty Base)
    (R : Fin (Versioning.compilePacketLocal graph).blocks.length → Ty Base)
    (checked : packetLocalSourceChecks graph names ctx exits external R = true) :
    RoundTrip.PacketClosed graph ∧
      ∃ table, elaborate (Versioning.compilePacketLocal graph) exits (fun i => (names i, 0)) = some table ∧
        let profile := fun i => Ty.product (R i) .unit
        let types := SSA.FiniteSum.append profile external
        checkBody types ctx table.entry = true ∧
          ∀ i, checkBody types (.snoc ctx (profile i)) (table.block i) = true := by
  let compiled := Versioning.compilePacketLocal graph
  let labels := Versioning.destinationsWith graph (fun _ => [])
  let build := Versioning.compileBlockWith (F := F) labels [] []
  let index := labelIndex compiled.blocks exits
  let profile := fun i => Ty.product (R i) .unit
  let old := SSA.FiniteSum.append R external
  let new := SSA.FiniteSum.append profile external
  have route : Routes index labels (fun _ => []) old new :=
    routes_saved graph exits (fun _ => []) build (fun _ => []) (fun _ => []) R external
      (fun _ => rfl) (fun _ _ _ => rfl)
  obtain ⟨sourceEntry, sourceBlocks⟩ := Bool.and_eq_true_iff.mp checked
  have closed : RoundTrip.PacketClosed graph := by
    intro item member
    obtain ⟨j, hj, eq⟩ := List.getElem_of_mem member
    let i : Fin compiled.blocks.length := Fin.cast (List.length_map _).symm ⟨j, hj⟩
    obtain ⟨_, read, _⟩ := checked_source (List.all_eq_true.mp sourceBlocks i (List.mem_finRange i))
    rw [← eq]
    exact block_packetClosed _ read
  obtain ⟨_, read, typed⟩ := checked_source sourceEntry
  obtain ⟨entry, hEntry, tEntry⟩ := version_body index labels (fun _ => []) [] old new route []
    graph.entry 0 (fun _ => 0) _ _ _ _ (entry_scope names ctx)
    (by simp [SavedScope]) (by simp [KeepsCapture]) (by simp [Supplies]) read typed
  have byBlock (i : Fin compiled.blocks.length) :
      ∃ flat, body index (blockNames compiled.blocks[i].2.param) compiled.blocks[i].2.body = some flat ∧
        checkBody new (.snoc ctx (profile i)) flat = true := by
    let j : Fin graph.blocks.length := Fin.cast (List.length_map _) i
    have checkAt := List.all_eq_true.mp sourceBlocks i (List.mem_finRange i)
    have row : compiled.blocks[i].2 = build graph.blocks[j].2 := by
      exact congrArg Prod.snd (List.getElem_map (fun item => (item.1, build item.2))
        (l := graph.blocks) (i := i.val) (h := by rw [List.length_map]; exact j.isLt))
    rw [row]
    exact block_checkedWith labels [] graph.blocks[j].2 index old new (fun _ => []) [] route
      ctx (R i) (by simp) (by simp [KeepsCapture]) (by simp [Supplies]) checkAt
  obtain ⟨rows, hRows, tRows⟩ := tabulate_checked byBlock
  exact ⟨closed, ⟨entry, rows⟩, by
    unfold elaborate
    change (body index (first fun i => (names i, 0)) compiled.entry).bind _ = _
    rw [show body index (first fun i => (names i, 0)) compiled.entry = some entry
      from hEntry]
    exact congrArg (Option.map (FiniteCFG.mk entry)) hRows, tEntry, tRows⟩

end PacketLocal

variable {κ Label : Type (u + 1)} [DecidableEq Label] [DecidableEq κ]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List Label} {external : Fin exits.length → Ty κ}
  {fields : Label → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

omit [DecidableEq κ] in
private theorem packetProfile_saved (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slots : List (Fin n)) (i : Fin (versioned).blocks.length)
    (layout : a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register))) :
    a.packetProfile R saved i =
      .product (R (Fin.cast a.reversionCount i)) (LiveOut.recordType (captureFields context slots)) := by
  let typed := fun reg : Register => (reg, if bound : reg.down < n then
    context.get ⟨reg.down, bound⟩ else Ty.unit)
  have fieldsEq : (a.savedRegisters i).attach.map (fun reg =>
      (reg.val, context.get ⟨reg.val.down, saved i reg.val reg.property⟩)) =
      (a.savedRegisters i).map typed := by
    rw [← List.attach_map_val (l := a.savedRegisters i) (f := typed)]
    apply List.map_congr_left
    intro reg _
    simp [typed, saved i reg.val reg.property]
  have types : (slots.map (fun j => (⟨j.val⟩ : Register))).map typed = captureFields context slots := by
    simp only [captureFields, List.map_map]
    apply List.map_congr_left
    intro j _
    simp [typed, j.isLt]
  simp only [Lowered.packetProfile, fieldsEq, layout, types]

omit [DecidableEq κ] in
private theorem entry_saved (slots : List (Fin n)) :
    SavedScope (fun _ => 0) (captureFields context slots)
      (first fun i : Fin n => ((⟨i.val⟩ : Register), (0 : Nat))) context := by
  intro reg A field
  obtain ⟨j, _, eq⟩ := List.mem_map.mp field
  cases eq
  refine ⟨j, ?_, rfl⟩
  unfold first
  cases hit : (List.finRange n).find? (fun k => decide
      (((⟨k.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0))) with
  | none =>
    have := List.find?_eq_none.mp hit j (by simp)
    simp at this
  | some i =>
    have eq : ((⟨i.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0) :=
      of_decide_eq_true (List.find?_some
        (p := fun k : Fin n => decide (((⟨k.val⟩ : Register), (0 : Nat)) = (⟨j.val⟩, 0))) hit)
    exact congrArg some (Fin.ext (congrArg (ULift.down ∘ Prod.fst) eq))

omit [DecidableEq κ] [DecidableEq Label] in
private theorem kept_body (src : CFG.Body Register Label P.Instr) (slots : List (Fin n))
    (kept : ∀ i ∈ slots, (⟨i.val⟩ : Register) ∉ src.toRegion.bound) :
    KeepsCapture (captureFields context slots) src.toRegion := by
  intro reg A field
  obtain ⟨i, member, eq⟩ := List.mem_map.mp field
  cases eq
  exact kept i member

omit [DecidableEq κ] in
private theorem fields_subset (available needed : List (Fin n)) (subset : needed ⊆ available) :
    captureFields context needed ⊆ captureFields context available := by
  intro field member
  obtain ⟨i, hit, eq⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨i, subset hit, eq⟩

omit [DecidableEq κ] in
private theorem destination_subset
    (entrySlots : List (Fin n)) (layouts : Fin (versioned).blocks.length → List (Fin n))
    (projections : ∀ i, List.Sublist (layouts i) entrySlots) (label : Label) :
    destinationSlots a layouts label ⊆ entrySlots := by
  unfold destinationSlots
  cases (versioned).blocks.findFinIdx? (fun item => label == item.1) with
  | none => simp
  | some i => exact (projections i).subset

set_option maxHeartbeats 400000 in
theorem compiled_success_projected (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (entrySlots : List (Fin n)) (layouts : Fin (versioned).blocks.length → List (Fin n))
    (layout : ∀ i, a.savedRegisters i = (layouts i).map (fun j => (⟨j.val⟩ : Register)))
    (projections : ∀ i, List.Sublist (layouts i) entrySlots)
    (kept : keepsEntryCaptures a entrySlots = true)
    (edges : checksCaptureEdges a layouts = true)
    (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  let index := labelIndex (versioned).blocks exits
  let captures : Fin n → Register := fun i => ⟨i.val⟩
  let original := fun i => R (Fin.cast a.reversionCount i)
  let savedFields := fun i => captureFields context (layouts i)
  let required := fun label => captureFields context (destinationSlots a layouts label)
  let expanded := fun i => Ty.product (original i) (LiveOut.recordType (savedFields i))
  have profile : a.packetProfile R saved = expanded :=
    funext (fun i => packetProfile_saved a R saved (layouts i) i (layout i))
  rw [profile]
  let old := SSA.FiniteSum.append original exitTypes
  let new := SSA.FiniteSum.append expanded exitTypes
  have savedAt (i : Fin (attached).blocks.length) :
      Versioning.slots attached (attached).blocks[i].2 =
        (savedFields (Fin.cast (List.length_map _).symm i)).map Prod.fst := by
    exact (layout (Fin.cast (List.length_map _).symm i)).trans
      (by simp [savedFields, captureFields, Function.comp_def])
  have route := routes_saved attached exits (Versioning.slots attached) (Versioning.compileBlock attached)
    savedFields required original exitTypes savedAt
    (by
      intro k i found
      have hit : (versioned).blocks.findFinIdx? (fun item => k == item.1) = some i := found
      simp [required, destinationSlots, hit, savedFields]
      rfl)
  have keptAt := List.all_eq_true.mp kept
  have entryKeeps := kept_body (context := context) (attached).entry entrySlots fun j hit =>
    of_decide_eq_true (Bool.and_eq_true_iff.mp (keptAt j hit)).1
  have entrySupplies : Supplies required (captureFields context entrySlots) (attached).entry.targets :=
    fun k _ => fields_subset entrySlots _ (destination_subset a entrySlots layouts projections k)
  obtain ⟨sourceEntry, sourceBlocks⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨_, read, typed⟩ := checked_source sourceEntry
  obtain ⟨entry, hEntry, tEntry⟩ := version_body index _ required (captureFields context entrySlots)
    old new route (Versioning.registers attached) (attached).entry 0 (fun _ => 0) _ _ _ _
    (entry_scope captures context) (entry_saved (context := context) entrySlots) entryKeeps entrySupplies read typed
  have byBlock (i : Fin (versioned).blocks.length) :
      ∃ flat, body index (blockNames ((versioned).blocks[i].2.param)) (versioned).blocks[i].2.body = some flat ∧
        checkBody new (.snoc context (expanded i)) flat = true := by
    let j : Fin (attached).blocks.length := Fin.cast (List.length_map _) i
    have checkAt := List.all_eq_true.mp sourceBlocks i (List.mem_finRange i)
    have row : (versioned).blocks[i].2 = Versioning.compileBlock attached (attached).blocks[j].2 := by
      exact congrArg Prod.snd (List.getElem_map
        (fun item => (item.1, Versioning.compileBlock attached item.2))
        (l := (attached).blocks) (i := i.val) (h := by
          rw [List.length_map]
          exact j.isLt))
    rw [row]
    have bodyKeeps := kept_body (context := context) (attached).blocks[j].2.body (layouts i) fun k hit =>
      of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (keptAt k ((projections i).subset hit))).2 _
        (List.getElem_mem (l := (attached).blocks) j.isLt))
    have bodySupplies : Supplies required (savedFields i) (attached).blocks[j].2.body.targets := by
      intro k hit
      apply fields_subset
      have row := List.all_eq_true.mp edges i (by simp)
      have requested := List.all_eq_true.mp row k hit
      exact fun slot member => of_decide_eq_true (List.all_eq_true.mp requested slot member)
    exact block_checked attached (attached).blocks[j].2 index old new required (savedFields i) route
      context (original i) (savedAt j) bodyKeeps bodySupplies checkAt
  obtain ⟨rows, hRows, tRows⟩ := tabulate_checked byBlock
  exact ⟨⟨entry, rows⟩, by
    unfold compile elaborate
    change (body index (first fun i => (captures i, 0)) (versioned).entry).bind
      (fun outgoing => (tabulate (versioned).blocks.length
        (fun i => body index (blockNames (versioned).blocks[i].2.param)
          (versioned).blocks[i].2.body)).map (FiniteCFG.mk outgoing)) = some (FiniteCFG.mk entry rows)
    rw [show body index (first fun i => (captures i, 0)) (versioned).entry = some entry from hEntry]
    exact congrArg (Option.map (FiniteCFG.mk entry)) hRows, tEntry, tRows⟩

theorem compiled_success_captures (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slots : List (Fin n))
    (layout : ∀ i, a.savedRegisters i = slots.map (fun j => (⟨j.val⟩ : Register)))
    (kept : keepsEntryCaptures a slots = true) (checked : checks a R = true) :
    ∃ table, compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
  have subset (label : Label) := destination_subset a slots (fun _ => slots)
    (fun _ => List.Sublist.refl slots) label
  apply compiled_success_projected a R saved slots (fun _ => slots) layout
    (fun _ => List.Sublist.refl slots) kept _ checked
  exact List.all_eq_true.mpr fun _ _ => List.all_eq_true.mpr fun label _ =>
    List.all_eq_true.mpr fun slot member => decide_eq_true (subset label member)

omit [DecidableEq κ] in
theorem empty_of_no_captures (closed : n = 0) (saved : a.SavesCaptures) :
    ∀ i, a.savedRegisters i = [] := by
  intro i
  cases shape : a.savedRegisters i with
  | nil => rfl
  | cons r rs =>
    have bound := saved i r (by simp [shape])
    omega

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

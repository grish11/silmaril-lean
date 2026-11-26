module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v w

private theorem val_mem_fv {V : Type w} [DecidableEq V] (a : Val V) (x : V) :
    x ∈ a.fvList ↔ x ∈ a.fv := by
  induction a <;> simp [Val.fvList, Val.fv, *]

private theorem op_mem_fv {V : Type w} {F : Type v} [DecidableEq V] (a : Op V F) (x : V) :
    x ∈ a.fvList ↔ x ∈ a.fv := by
  cases a <;> simp [Op.fvList, Op.fv, val_mem_fv]

private theorem region_mem_fv {V K : Type w} {F : Type v} [DecidableEq V]
    (r : Silmaril.SSA.LambdaRTL.Region V K F) (x : V) : x ∈ r.fvList ↔ x ∈ r.fv := by
  induction r <;>
    simp [Silmaril.SSA.LambdaRTL.Region.fvList, Silmaril.SSA.LambdaRTL.Region.fv, val_mem_fv,
      op_mem_fv, *, and_assoc, and_comm]

section Readback

variable {V K : Type w} {F : Type v} {labels : Nat} [DecidableEq V]
  {index : K → Option (Fin labels)}

omit [DecidableEq V] in
private theorem value_reads {n : Nat} {names : Names V n} {val : Val V} {out : _}
    (read : value (F := F) names val = some out) (reg : V) (member : reg ∈ val.fvList) :
    (names reg).isSome = true := by
  induction val generalizing out with
  | var x =>
    have eq : reg = x := by simpa [Val.fvList] using member
    subst reg
    obtain ⟨i, found, _⟩ := Option.map_eq_some_iff.mp read
    simp [found]
  | unit => simp [Val.fvList] at member
  | pair a b ihA ihB =>
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, left, _, right, _⟩ := read
    rcases List.mem_append.mp member with used | used
    · exact ihA left used
    · exact ihB right used

omit [DecidableEq V] in
private theorem operand_reads {n : Nat} {names : Names V n} {op : Op V F} {out : _}
    (read : operand names op = some out) (reg : V) (member : reg ∈ op.fvList) :
    (names reg).isSome = true := by
  cases op with
  | val a => exact value_reads read reg member
  | app f a =>
    obtain ⟨_, h, _⟩ := Option.map_eq_some_iff.mp read
    exact value_reads h reg member
  | inl | inr | abort => cases read

private theorem parent_reads {n : Nat} {names : Names V n} {binder reg : V}
    (ne : reg ≠ binder) (read : (bindName names binder reg).isSome = true) :
    (names reg).isSome = true := by
  simpa [bindName, ne] using read

private theorem term_reads {n : Nat} {names : Names V n} {tail : CFG.Term V K F} {out : _}
    (read : term index names tail = some out) (reg : V) (member : reg ∈ tail.toRegion.fvList) :
    (names reg).isSome = true := by
  induction tail generalizing n with
  | br k val =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, _, _, found, _⟩ := read
    exact value_reads found reg member
  | case discr x left y right ihL ihR =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, op, _, l, _, r, _⟩ := read
    simp only [CFG.Term.toRegion, Silmaril.SSA.LambdaRTL.Region.fvList, List.mem_append,
      List.mem_filter, decide_eq_true_eq] at member
    rcases member with (used | ⟨used, ne⟩) | ⟨used, ne⟩
    · exact operand_reads op reg used
    · exact parent_reads ne (ihL l used)
    · exact parent_reads ne (ihR r used)

private theorem body_reads {n : Nat} {names : Names V n} {src : CFG.Body V K F} {out : _}
    (read : body index names src = some out) (reg : V) (member : reg ∈ src.toRegion.fvList) :
    (names reg).isSome = true := by
  induction src generalizing n with
  | term tail => exact term_reads read reg member
  | let1 x op tail ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, hOp, _, hTail, _⟩ := read
    simp only [CFG.Body.toRegion, Silmaril.SSA.LambdaRTL.Region.fvList, List.mem_append,
      List.mem_filter, decide_eq_true_eq] at member
    rcases member with used | ⟨used, ne⟩
    · exact operand_reads hOp reg used
    · exact parent_reads ne (ih hTail used)
  | let2 x y op tail ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, hOp, _, hTail, _⟩ := read
    simp only [CFG.Body.toRegion, Silmaril.SSA.LambdaRTL.Region.fvList, List.mem_append,
      List.mem_filter, decide_eq_true_eq] at member
    rcases member with used | ⟨used, hX, hY⟩
    · exact operand_reads hOp reg used
    · exact parent_reads hX (parent_reads hY (ih hTail used))

end Readback

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "g" => withLiveOut (P := P) fields a.source

private theorem entry_scope : ∀ reg ∈ (g).entry.toRegion.fvList, reg.down < n := by
  let index := fun label => (labelIndex (g).blocks exits label).map
    (Fin.cast (congrArg (· + exits.length) a.count))
  let names : Names Register.{u} n := first (fun i : Fin n => (⟨i.val⟩ : Register))
  let readBlocks := tabulate blocks fun i =>
    let block := (g).blocks[Fin.cast a.count.symm i].2
    body index (blockNames (n := n) block.param) block.body
  have readback : ((body index names (g).entry).bind fun entry =>
      readBlocks.map fun rows => ⟨entry, rows⟩) = some code := a.readback
  obtain ⟨_, entry, _⟩ := Option.bind_eq_some_iff.mp readback
  intro reg used
  have found : (first (fun i : Fin n => (⟨i.val⟩ : Register)) reg).isSome = true :=
    body_reads entry reg used
  cases read : first (fun i : Fin n => (⟨i.val⟩ : Register)) reg with
  | none => simp [read] at found
  | some i =>
    have eq : (⟨i.val⟩ : Register) = reg :=
      of_decide_eq_true (List.find?_some (p := fun j : Fin n => decide ((⟨j.val⟩ : Register) = reg)) read)
    exact (congrArg ULift.down eq) ▸ i.isLt

theorem saves_captures
    (entry : ∀ reg ∈ (g).entry.toRegion.fvList, reg.down < n)
    (params : ∀ item ∈ (g).blocks, item.2.param = (freshRegisters n).parameter) :
    a.SavesCaptures := by
  intro i reg member
  let j : Fin (g).blocks.length := Fin.cast (List.length_map _) i
  change reg ∈ Versioning.slots g (g).blocks[j].2 at member
  obtain ⟨support, notParam⟩ := List.mem_filter.mp member
  have param := params _ (List.getElem_mem (l := (g).blocks) j.isLt)
  simp only [Versioning.registers, List.mem_dedup, List.mem_append, List.mem_flatMap] at support
  rcases support with used | ⟨item, inTable, used⟩
  · exact entry reg used
  · have eq : reg = item.2.param :=
      Finset.mem_singleton.mp (a.closed item inTable ((region_mem_fv _ _).mp used))
    simp [eq, params item inTable, param] at notParam

theorem saves_captures_of_lowerFresh [DecidableEq P.Instr] (internal : Fin blocks → K)
    (accepted : lowerFresh internal context exits external fields code = some a) :
    a.SavesCaptures := by
  apply saves_captures a (entry_scope a)
  change (lower (freshRegisters n) (fun i : Fin n => (⟨i.val⟩ : Register)) internal
    (fun i => exits[i]) code).bind _ = some a at accepted
  obtain ⟨source, lowered, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  have eq : source = a.source := by
    dsimp only at accepted
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    split at accepted <;> try contradiction
    exact congrArg Lowered.source (Option.some.inj accepted)
  let target := SSA.FiniteSum.append internal (fun i : Fin exits.length => exits[i])
  let isInternal := SSA.FiniteSum.append (fun _ : Fin blocks => true)
    (fun _ : Fin exits.length => false)
  change (lowerBody (freshRegisters n) target isInternal (fun i => some ⟨i.val⟩) 0 code.entry).bind
    (fun entry => (tabulate blocks fun i =>
      lowerBody (freshRegisters n) target isInternal
        (Fin.cases (some (freshRegisters n).parameter) (fun _ => none)) 0 (code.block i)).bind
      fun rows => some ⟨entry, List.ofFn fun i => (internal i, ⟨(freshRegisters n).parameter, rows i⟩)⟩)
    = some source at lowered
  obtain ⟨entry, _, rest⟩ := Option.bind_eq_some_iff.mp lowered
  obtain ⟨bodies, _, same⟩ := Option.bind_eq_some_iff.mp rest
  cases Option.some.inj same
  intro item member
  rw [← eq] at member
  simp only [withLiveOut, LiveOut.attach, List.mem_map, List.mem_ofFn] at member
  obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := member
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse

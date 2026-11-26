module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Admission

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.SSA.LambdaRTL (CFG Val Op)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (Flat FiniteCFG)
open LetCase.LocallyNameless (Tm HasType)

variable {F : Type} {labels n m : Nat} [HasTy F PacketType]

-- Old lookups are supported at the same index and exact type. Unused slots
-- in the ambient contexts do not have to match.
private def Scope (old : Names Register n) (new : Names Register m)
    (ctx : BoundCtx PacketType n) (next : BoundCtx PacketType m) : Prop :=
  ∀ reg i, old reg = some i →
    ∃ j, new reg = some j ∧ j.val = i.val ∧ next.get j = ctx.get i

private theorem Scope.bind {old : Names Register n} {new : Names Register m}
    {ctx : BoundCtx PacketType n} {next : BoundCtx PacketType m}
    (scope : Scope old new ctx next) (reg : Register) (ty : PacketType) :
    Scope (bindName old reg) (bindName new reg) (.snoc ctx ty) (.snoc next ty) := by
  intro x i lookup
  by_cases same : x = reg
  · simp only [bindName, ite_eq_left same, Option.some.injEq] at lookup
    subst i
    exact ⟨0, by simp [bindName, same], rfl, rfl⟩
  · simp only [bindName, ite_eq_right same, Option.map_eq_some_iff] at lookup
    obtain ⟨k, hk, rfl⟩ := lookup
    obtain ⟨j, hj, position, type⟩ := scope x k hk
    exact ⟨j.succ, by simp [bindName, same, hj], congrArg Nat.succ position, type⟩

private theorem value_checked {old : Names Register n} {new : Names Register m}
    {ctx : BoundCtx PacketType n} {next : BoundCtx PacketType m}
    (scope : Scope old new ctx next) (v : Val Register) {a : Tm Empty F n} {ty : PacketType}
    (read : value old v = some a) (typed : HasType F .nil ctx a ty) :
    ∃ b : Tm Empty F m, value new v = some b ∧ infer next b = some ty ∧
      Morphism.CaseSSA.erase b = Morphism.CaseSSA.erase a := by
  induction v generalizing a ty with
  | var reg =>
    simp only [value, Option.map_eq_some_iff] at read
    obtain ⟨i, hi, rfl⟩ := read
    cases typed
    obtain ⟨j, hj, position, type⟩ := scope reg i hi
    exact ⟨.bv j, by simp [value, hj], congrArg some type, congrArg LambdaSSA.Tm.var position⟩
  | unit =>
    cases read
    cases typed
    exact ⟨.unit, rfl, rfl, rfl⟩
  | pair l r ihl ihr =>
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨l', hl, r', hr, rfl⟩ := read
    cases typed with
    | pair tl tr =>
      obtain ⟨l'', el, il, rl⟩ := ihl hl tl
      obtain ⟨r'', er, ir, rr⟩ := ihr hr tr
      exact ⟨.pair l'' r'', by simp [value, el, er], by simp [infer, il, ir],
        congrArg₂ LambdaSSA.Tm.pair rl rr⟩

private theorem operand_checked {old : Names Register n} {new : Names Register m}
    {ctx : BoundCtx PacketType n} {next : BoundCtx PacketType m}
    (scope : Scope old new ctx next) (op : Op Register F) {a : Tm Empty F n} {ty : PacketType}
    (read : operand old op = some a) (typed : HasType F .nil ctx a ty) :
    ∃ b : Tm Empty F m, operand new op = some b ∧ infer next b = some ty ∧
      Morphism.CaseSSA.erase b = Morphism.CaseSSA.erase a := by
  cases op with
  | val v => exact value_checked scope v read typed
  | app f v =>
    simp only [operand, Option.map_eq_some_iff] at read
    obtain ⟨a, ha, rfl⟩ := read
    cases typed with
    | op typed =>
      obtain ⟨b, hb, checked, same⟩ := value_checked scope v ha typed
      exact ⟨.op f b, by simp [operand, hb], by simp [infer, checked],
        congrArg (LambdaSSA.Tm.op f) same⟩
  | inl | inr | abort => cases read

variable {K : Type 1} (index : K → Option (Fin labels)) (types : Fin labels → PacketType)

private theorem term_checked (tail : CFG.Term Register K F) {old : Names Register n} {new : Names Register m}
    {ctx : BoundCtx PacketType n} {next : BoundCtx PacketType m} (scope : Scope old new ctx next)
    {a : Flat F labels n} (read : term index old tail = some a) (typed : a.HasType types ctx) :
    ∃ b, term index new tail = some b ∧ checkBody types next b = true ∧ b.erase = a.erase := by
  induction tail generalizing n m with
  | br label v =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨dest, hd, arg, ha, rfl⟩ := read
    cases typed with
    | br typed =>
      obtain ⟨b, hb, checked, same⟩ := value_checked scope v ha typed
      exact ⟨.br dest b, by simp [term, hd, hb], by simp [checkBody, checked],
        congrArg (LambdaSSA.Region.br dest.val) same⟩
  | case op x l y r ihl ihr =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨a, ha, l', hl, r', hr, rfl⟩ := read
    cases typed with
    | case test left right =>
      obtain ⟨b, hb, cb, eb⟩ := operand_checked scope op ha test
      obtain ⟨l'', hL, cL, eL⟩ := ihl (scope.bind x _) hl left
      obtain ⟨r'', hR, cR, eR⟩ := ihr (scope.bind y _) hr right
      exact ⟨.case b l'' r'', by simp [term, hb, hL, hR], by simp [checkBody, cb, cL, cR],
        by simp only [Flat.erase, eb, eL, eR]⟩

private theorem body_checked (block : CFG.Body Register K F)
    {old : Names Register n} {new : Names Register m}
    {ctx : BoundCtx PacketType n} {next : BoundCtx PacketType m} (scope : Scope old new ctx next)
    {a : Flat F labels n} (read : body index old block = some a) (typed : a.HasType types ctx) :
    ∃ b, body index new block = some b ∧ checkBody types next b = true ∧ b.erase = a.erase := by
  induction block generalizing n m with
  | term tail => exact term_checked index types tail scope read typed
  | let1 x op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨a, ha, rest', hr, rfl⟩ := read
    cases typed with
    | let₁ opType restType =>
      obtain ⟨b, hb, cb, eb⟩ := operand_checked scope op ha opType
      obtain ⟨rest'', hR, cR, eR⟩ := ih (scope.bind x _) hr restType
      exact ⟨.let₁ b rest'', by simp [body, hb, hR], by simp [checkBody, cb, cR],
        by simp only [Flat.erase, eb, eR]⟩
  | let2 x y op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨a, ha, rest', hr, rfl⟩ := read
    cases typed with
    | let₂ opType restType =>
      obtain ⟨b, hb, cb, eb⟩ := operand_checked scope op ha opType
      obtain ⟨rest'', hR, cR, eR⟩ := ih ((scope.bind x _).bind y _) hr restType
      exact ⟨.let₂ b rest'', by simp [body, hb, hR], by simp [checkBody, cb, cR],
        by simp only [Flat.erase, eb, eR]⟩


private theorem packet_scope {n m : Nat} (param : Register)
    (ctx : BoundCtx PacketType n) (next : BoundCtx PacketType m) (payload : PacketType) :
    Scope (blockNames param) (blockNames param) (.snoc ctx payload) (.snoc next payload) :=
  (show Scope (fun _ => none) (fun _ => none) ctx next from fun _ _ h => by cases h).bind param payload

private theorem tabulate_some {A : Type} {count : Nat} {f : Fin count → Option A}
    {rows : Fin count → A} (read : ∀ i, f i = some (rows i)) :
    tabulate count f = some rows := by
  induction count with
  | zero =>
    exact congrArg some (funext fun i => i.elim0)
  | succ n ih =>
    simp only [tabulate, read 0, Option.bind_some, ih (fun i => read i.succ), Option.map_some]
    exact congrArg some (funext fun i => Fin.cases rfl (fun _ => rfl) i)

private theorem first_numbered (i : Fin n) :
    first (fun j : Fin n => (⟨j.val⟩ : Register)) ⟨i.val⟩ = some i := by
  unfold first
  cases h : (List.finRange n).find? (fun j => decide ((⟨j.val⟩ : Register) = ⟨i.val⟩)) with
  | some j =>
    have hit : (⟨j.val⟩ : Register) = ⟨i.val⟩ :=
      of_decide_eq_true (List.find?_some (p := fun k : Fin n => decide ((⟨k.val⟩ : Register) = ⟨i.val⟩)) h)
    exact congrArg some (Fin.ext (congrArg ULift.down hit))
  | none =>
    have miss := List.find?_eq_none.mp h i (by simp)
    simp at miss

omit [HasTy F PacketType] in
theorem slot_type {V : Type 1} {k : Nat} {seed : Val (Fin k)} {ty : PacketType}
    (names : Fin k → V) (s : StructuralSeed seed ty) (i : Fin (s.footprint names).length) :
    (BoundCtx.ofFin (fun j : Fin (s.footprint names).length => (s.footprint names)[j.val].2)).get i =
      (s.footprint names)[i.val].2 :=
  congrFun (BoundCtx.get_ofFin _) i

private theorem infer_occurrence {V : Type 1} {k : Nat} {seed : Val (Fin k)} {ty : PacketType}
    (names : Fin k → V) (s : StructuralSeed seed ty) (ctx : BoundCtx PacketType n) (offset : Nat)
    (slots : ∀ i : Fin (s.footprint names).length, ∃ j : Fin n,
      j.val = offset + i.val ∧ ctx.get j = (s.footprint names)[i.val].2) :
    ∃ t : Tm Empty F n, value (first (fun j => (⟨j.val⟩ : Register))) (s.occurrenceOperand names offset) =
      some t ∧ infer ctx t = some ty := by
  induction s generalizing offset with
  | var i ty =>
    obtain ⟨j, position, type⟩ := slots ⟨0, by simp [StructuralSeed.footprint]⟩
    simp only [Nat.add_zero] at position
    exact ⟨.bv j, by simp [StructuralSeed.occurrenceOperand, value, ← position, first_numbered],
      congrArg some type⟩
  | unit => exact ⟨.unit, rfl, rfl⟩
  | pair l r ihl ihr =>
    obtain ⟨a, ha, ca⟩ := ihl offset (fun i => by
      have hin : i.val < ((StructuralSeed.pair l r).footprint names).length := by
        simp only [StructuralSeed.footprint, List.length_append]
        omega
      obtain ⟨j, pos, ht⟩ := slots ⟨i.val, hin⟩
      exact ⟨j, pos, ht.trans (congrArg Prod.snd (List.getElem_append_left i.isLt))⟩)
    obtain ⟨b, hb, cb⟩ := ihr (offset + (l.footprint names).length) (fun i => by
      have hin : (l.footprint names).length + i.val < ((StructuralSeed.pair l r).footprint names).length := by
        simp only [StructuralSeed.footprint, List.length_append]
        exact Nat.add_lt_add_left i.isLt _
      obtain ⟨j, pos, ht⟩ := slots ⟨(l.footprint names).length + i.val, hin⟩
      refine ⟨j, by simpa only [Nat.add_assoc] using pos, ht.trans ?_⟩
      simp only [StructuralSeed.footprint, List.getElem_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left])
    exact ⟨.pair a b, by simp [StructuralSeed.occurrenceOperand, value, ha, hb], by simp [infer, ca, cb]⟩

variable {V L : Type 1} [DecidableEq V] [DecidableEq L]
  {signature : PrimitiveSignature F} {source : CFG V L F} {exits : List L} {fields : L → List V}
  {ty : PacketType} {outputs : Fin exits.length → PacketType}
  (entry : StructuralEntry signature source exits fields ty outputs)

omit [HasTy F PacketType] in
theorem compile_operand : letI := signature.typing
    ∃ t : Tm Empty F entry.footprint.length, value (first entry.occurrenceNames) entry.occurrenceOperand =
      some t ∧ infer entry.occurrenceContext t = some ty :=
  letI := signature.typing
  infer_occurrence (fun i => entry.names[i.val]) entry.typedSeed entry.occurrenceContext 0
    (fun i => ⟨i, (Nat.zero_add _).symm, slot_type _ _ i⟩)

private theorem bv_type {ctx : BoundCtx PacketType n} {i : Fin n} {ty : PacketType}
    (typed : HasType F .nil ctx (.bv i : Tm Empty F n) ty) : ctx.get i = ty := by
  cases typed
  rfl

omit [HasTy F PacketType] in
theorem reconstruct (packetType : entry.entry.context.get entry.provenance.slot = ty) :
    letI := signature.typing
    ∃ (code : FiniteCFG F entry.occurrenceGraph.blocks.length entry.program.exits.length entry.footprint.length)
      (dest : Fin (entry.occurrenceGraph.blocks.length + entry.program.exits.length))
      (packet : Tm Empty F entry.footprint.length),
      elaborate entry.occurrenceGraph entry.program.exits entry.occurrenceNames = some code ∧
      check code entry.occurrenceContext entry.entry.blocks entry.entry.exits = true ∧
      code.entry = .br dest packet ∧ dest.val = entry.provenance.start.val ∧
      ∀ i, (code.block i).erase = (entry.entry.target.block i).erase := by
  let _ := signature.typing
  let graph := entry.program.compile 0
  let index := labelIndex graph.blocks entry.program.exits
  let types := SSA.FiniteSum.append entry.entry.blocks entry.entry.exits
  have admitted := entry.entry.accepted
  change ((term index (first entry.entry.captures)
      (.br ⟨entry.program.entry 0⟩ (.var ⟨0⟩))).bind fun start =>
      (tabulate graph.blocks.length fun i =>
        body index (blockNames graph.blocks[i].2.param) graph.blocks[i].2.body).map
        fun rows => (⟨start, rows⟩ : FiniteCFG F _ _ _)) = some entry.entry.target at admitted
  simp only [term, value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at admitted
  obtain ⟨start, ⟨dest, route, arg, ⟨slot, lookup, rfl⟩, rfl⟩, rows, table, exactCode⟩ := admitted
  have entryEq : entry.entry.target.entry = .br dest (.bv slot) :=
    (congrArg FiniteCFG.entry exactCode).symm
  have rowsEq : entry.entry.target.block = rows := (congrArg FiniteCFG.block exactCode).symm
  have destination : dest.val = entry.provenance.start.val ∧ slot.val = entry.provenance.slot.val := by
    simpa only [entryEq, Flat.erase, Morphism.CaseSSA.erase, LambdaSSA.Region.br.injEq,
      LambdaSSA.Tm.var.injEq] using entry.provenance.publicEntry
  have startType : types dest = ty := by
    have typed := entry.entry.typed.entry
    rw [entryEq] at typed
    cases typed with
    | br argType =>
      exact (bv_type argType).symm.trans ((congrArg entry.entry.context.get (Fin.ext destination.2)).trans packetType)
  have checkedRows (i : Fin graph.blocks.length) := body_checked index types graph.blocks[i].2.body
    (packet_scope graph.blocks[i].2.param entry.entry.context entry.occurrenceContext (entry.entry.blocks i))
    ((tabulate_at table i).trans (congrArg some (congrFun rowsEq i)).symm) (entry.entry.typed.block i)
  choose newRows newRead newCheck sameRows using checkedRows
  obtain ⟨packet, packetRead, packetChecked⟩ := compile_operand entry
  let code : FiniteCFG F graph.blocks.length entry.program.exits.length entry.footprint.length :=
    ⟨.br dest packet, newRows⟩
  refine ⟨code, dest, packet, ?_, ?_, rfl, destination.1, sameRows⟩
  · change ((term index (first entry.occurrenceNames) (.br ⟨entry.program.entry 0⟩ entry.occurrenceOperand)).bind
        fun start => (tabulate graph.blocks.length fun i =>
          body index (blockNames graph.blocks[i].2.param) graph.blocks[i].2.body).map
          fun rows => (⟨start, rows⟩ : FiniteCFG F _ _ _)) = some code
    simp [term, route, packetRead, code]
    exact tabulate_some newRead
  · simp only [check, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun i _ => newCheck i⟩
    change checkBody types entry.occurrenceContext (.br dest packet) = true
    simp [checkBody, packetChecked, startType]


omit [HasTy F PacketType] in
theorem admitted (packetType : entry.entry.context.get entry.provenance.slot = ty) :
    entry.admitOccurrences.isSome = true := by
  obtain ⟨code, _, _, elaborated, checked, _, _, _⟩ := reconstruct entry packetType
  unfold StructuralEntry.admitOccurrences
  split
  · rename_i failed
    rw [elaborated] at failed
    cases failed
  · rename_i actual elaboratedActual
    have same := Option.some.inj (elaboratedActual.symm.trans elaborated)
    subst actual
    simp [checked]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Admission

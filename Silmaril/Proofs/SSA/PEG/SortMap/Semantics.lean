module

public import Silmaril.SSA.PEG.SortMap.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.SortMap.Structure

public section

namespace Silmaril.SSA.PEG.SortMapProofs

open RVSDG (Tuple)

universe u u' v v' w

variable {D : Type u} {E : Type u'} {f : D → E}
variable {P : InstructionSet.{u,v} D} {Q : InstructionSet.{u',v'} E}
variable {params results ins : List (Ty D)} {n l : Nat} {out : Ty D}

private theorem map_symm {A B : Type w} (e : A ≃ B) (o : Option B) :
    (o.map e.symm).map e = o := by cases o <;> simp

private theorem monotonize_map {A B : Type w} (k : Nat) (e : A → B) (s : Nat → Option A) :
    monotonize (fun j => (s j).map e) k = (monotonize s k).map e := by
  unfold monotonize
  simp only [Option.isSome_map]
  split <;> rfl

private theorem read_ref {carrier : E → Type w} {sort : Fin n → Ty D} (r : Ref sort out)
    (v : Option ((sort r.id).Value (carrier ∘ f))) :
    (r.mapData f).read carrier (v.map (Ty.valueMapEquiv f carrier (sort r.id))) =
      (r.read (carrier ∘ f) v).map (Ty.valueMapEquiv f carrier out) := by
  obtain ⟨id, typed⟩ := r
  cases typed
  rfl

private def collectRefs {A : Ty D → Type w} {sort : Fin n → Ty D}
    (read : ∀ t, Ref sort t → Option (A t)) :
    {ts : List (Ty D)} → Tuple (Ref sort) ts → Option (Tuple A ts)
  | _, .nil => some .nil
  | _, .cons x xs => (read _ x).bind fun value => (collectRefs read xs).map (.cons value)

private theorem collect_refs {A : Ty D → Type w} {sort : Fin n → Ty D}
    (read : ∀ t, Ref sort t → Option (A t)) (args : Tuple (Ref sort) ins) :
    collect ins (fun j => read _ (args.get (portAt ins j))) = collectRefs read args := by
  induction args with
  | nil => rfl
  | @cons t ts x xs ih =>
    let args := Tuple.cons x xs
    have head : args.get (portAt (t :: ts) 0) = x := rfl
    have tail (j : Fin ts.length) :
        args.get (portAt (t :: ts) j.succ) = xs.get (portAt ts j) := rfl
    have remaining : (fun j : Fin ts.length => read _ (args.get (portAt (t :: ts) j.succ))) =
        (fun j : Fin ts.length => read _ (xs.get (portAt ts j))) :=
      funext fun j => congrArg (read _) (tail j)
    simp only [collect, show args = Tuple.cons x xs from rfl] at head remaining ⊢
    rw [head, remaining, ih]
    simp only [collectRefs]
    cases eq : read _ x with
    | none =>
      erw [eq]
      cases collectRefs read xs <;> rfl
    | some _ =>
      erw [eq]
      cases collectRefs read xs <;> rfl

private theorem collectRefs_transport {A : Ty D → Type w} {B : Ty E → Type w} {sort : Fin n → Ty D}
    (each : ∀ t, A t → B (t.mapData f)) (args : Tuple (Ref sort) ins)
    (source : ∀ t, Ref sort t → Option (A t))
    (target : ∀ t, Ref (Ty.mapData f ∘ sort) t → Option (B t))
    (agree : ∀ t (r : Ref sort t), target _ (r.mapData f) = (source _ r).map (each t)) :
    collectRefs target (mapDataTuple f (fun _ => Ref.mapData f) args) =
      (collectRefs source args).map (mapDataTuple f each) := by
  induction args with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapDataTuple, collectRefs, agree, ih]
    cases source _ x <;> cases collectRefs source xs <;> rfl

variable (op : ProfileMap f P Q) (m : Interpretation.{u',v',w} Q)

private theorem nodeEq {sort : Fin n → Ty D} (row : Node P params (Fin l) sort out)
    (input : Tuple (m.reductData op).Value params) (i : Index l)
    (source : ∀ t, Ref sort t → Index l → Option ((m.reductData op).Value t))
    (target : ∀ t, Ref (Ty.mapData f ∘ sort) t → Index l → Option (m.Value t))
    (agree : ∀ t (r : Ref sort t) j, target _ (r.mapData f) j =
      (source _ r j).map (Ty.valueMapEquiv f m.carrier t)) :
    let row' := row.mapData op
    row'.label.interpret m (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) i
      (fun slot j _ => target _ (row'.arg slot) j) =
    (row.label.interpret (m.reductData op) input i (fun slot j _ => source _ (row.arg slot) j)).map
      (Ty.valueMapEquiv f m.carrier out) := by
  obtain ⟨_, label, args⟩ := row
  cases label with
  | param p =>
    cases args
    exact congrArg some (get_mapDataTuple (Ty.valueMapEquiv f m.carrier ·) input p)
  | op instr =>
    rename_i ts
    let sourceAt := fun t r => source t r i
    let targetAt := fun t r => target t r i
    let mappedArgs := mapDataTuple f (fun _ => Ref.mapData f) args
    change (collect (Ty.mapProfile f ts) (fun j => targetAt _ (mappedArgs.get (portAt _ j)))).elim
      none (m.run (op instr)) =
        ((collect ts (fun j => sourceAt _ (args.get (portAt _ j)))).elim
          none ((m.reductData op).run instr)).map _
    rw [collect_refs targetAt mappedArgs, collect_refs sourceAt args,
      collectRefs_transport (Ty.valueMapEquiv f m.carrier ·) args sourceAt targetAt (fun t r => agree t r i)]
    cases collected : collectRefs sourceAt args with
    | none => erw [collected]; rfl
    | some values => erw [collected]; exact (map_symm _ _).symm
  | phi =>
    cases args
    rename_i flag arms
    cases arms
    rename_i yes tail
    cases tail
    rename_i no tail
    cases tail
    change (target _ (flag.mapData f) i).elim none
        (fun b => if b.down then target _ (yes.mapData f) i else target _ (no.mapData f) i) =
      ((source _ flag i).elim none (fun b => if b.down then source _ yes i else source _ no i)).map _
    rw [agree, agree, agree]
    cases source _ flag i with
    | none => rfl
    | some b =>
      rcases b with ⟨b⟩
      cases b <;> rfl
  | theta key =>
    cases args
    rename_i base tail
    cases tail
    rename_i step tail
    cases tail
    simp only [Node.mapData, Label.mapData, Label.interpret]
    generalize i key = k
    cases k with
    | zero => exact agree _ base i
    | succ k => exact agree _ step (i.set key k)
  | eval key =>
    cases args
    rename_i sampled tail
    cases tail
    rename_i count tail
    cases tail
    change (target _ (count.mapData f) i).elim none (fun k =>
      monotonize (fun j => target _ (sampled.mapData f) (i.set key j)) k.down) =
      ((source _ count i).elim none (fun k =>
      monotonize (fun j => source _ sampled (i.set key j)) k.down)).map _
    rw [agree]
    cases source _ count i with
    | none => rfl
    | some k =>
      change monotonize (fun j => target _ (sampled.mapData f) (i.set key j)) k.down = _
      have all (j : Nat) := agree _ sampled (i.set key j)
      simp only [all]
      exact monotonize_map k.down (Ty.valueMapEquiv f m.carrier out) _
  | pass key =>
    cases args
    rename_i flag tail
    cases tail
    change (firstTrue fun j => (target _ (flag.mapData f) (i.set key j)).map ULift.down).map ULift.up =
      ((firstTrue fun j => (source _ flag (i.set key j)).map ULift.down).map ULift.up).map _
    have same (j : Nat) : target _ (flag.mapData f) (i.set key j) = source _ flag (i.set key j) := by
      rw [agree]
      exact Option.map_id'
    simp only [same]
    exact Option.map_id'.symm

variable (g : Graph P params results n l)

theorem equation (input : Tuple (m.reductData op).Value params)
    (v : g.Valuation (m.reductData op)) (q : Request n l) :
    (g.mapData op).equation m (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) (g.mapDataValuation op m v) q =
      (g.equation (m.reductData op) input v q).map (Ty.valueMapEquiv f m.carrier (g.sort q.1)) :=
  nodeEq op m (g.node q.1) input q.2
    (fun _ r j => r.read (m.reductData op).carrier (v (r.id, j)))
    (fun _ r j => r.read m.carrier (g.mapDataValuation op m v (r.id, j)))
    (fun _ r j => read_ref (f := f) (carrier := m.carrier) r (v (r.id, j)))

theorem denote (input : Tuple (m.reductData op).Value params)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapData op).Demand) :
    (g.mapData op).denote m (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) mapped =
      g.mapDataValuation op m (g.denote (m.reductData op) input wf) := by
  apply (g.mapData op).solves_unique m _ mapped ((g.mapData op).denote_solves m _ mapped)
  intro q
  rw [equation]
  exact congrArg (fun x => x.map (Ty.valueMapEquiv f m.carrier (g.sort q.1)))
    (g.denote_solves (m.reductData op) input wf q)

private theorem roots_map {sort : Fin n → Ty D} (rs : Tuple (Ref sort) results)
    (v : ∀ t : Fin n, Option ((sort t).Value (m.carrier ∘ f))) :
    (mapDataTuple f (fun _ => Ref.mapData f) rs).map (fun _ r =>
        r.read m.carrier ((v r.id).map (Ty.valueMapEquiv f m.carrier (sort r.id)))) =
      mapDataTuple f (fun t x => x.map (Ty.valueMapEquiv f m.carrier t))
        (rs.map (fun _ r => r.read (m.carrier ∘ f) (v r.id))) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [mapDataTuple, Tuple.map]
    exact congrArg₂ Tuple.cons (read_ref r (v r.id)) ih

theorem observe (input : Tuple (m.reductData op).Value params) (i : Index l)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapData op).Demand) :
    (g.mapData op).observe m ((g.mapData op).denote m
      (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) input) mapped) i =
      mapDataTuple f (fun t x => x.map (Ty.valueMapEquiv f m.carrier t))
        (g.observe (m.reductData op) (g.denote (m.reductData op) input wf) i) := by
  rw [denote op m g input wf mapped]
  exact roots_map m g.roots (fun id => g.denote (m.reductData op) input wf (id, i))

end Silmaril.SSA.PEG.SortMapProofs

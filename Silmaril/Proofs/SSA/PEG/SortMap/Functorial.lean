module

public import Silmaril.SSA.PEG.SortMap.Defs
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.SortMapProofs

open RVSDG (Port Tuple)

universe u u' u'' v v' v'' w

variable {D : Type u} {E : Type u'} {F : Type u''}
variable {f : D → E} {g : E → F}
variable {P : InstructionSet.{u,v} D} {Q : InstructionSet.{u',v'} E}
variable {R : InstructionSet.{u'',v''} F}
variable {n l : Nat} {L : Type} {params ins results : List (Ty D)} {out : Ty D}

private theorem port_tail_heq {params params' : List (Ty F)} {t t' s s' : Ty F}
    (ht : t = t') (hp : params = params') (hs : s = s')
    {p : Port params t} {p' : Port params' t'} (h : HEq p p') :
    HEq (Port.tail (s := s) p) (Port.tail (s := s') p') := by
  subst t' params' s'
  cases h
  rfl

private theorem port_head_heq {params params' : List (Ty F)} {t t' : Ty F}
    (ht : t = t') (hp : params = params') :
    HEq (Port.head : Port (t :: params) t) (Port.head : Port (t' :: params') t') := by
  subst t' params'
  rfl

private theorem port_comp (p : Port params out) :
    HEq (mapDataPort g (mapDataPort f p)) (mapDataPort (g ∘ f) p) := by
  induction p with
  | head => exact port_head_heq (Ty.mapData_comp ..) (Ty.mapProfile_comp ..)
  | tail p ih => exact port_tail_heq (Ty.mapData_comp ..) (Ty.mapProfile_comp ..) (Ty.mapData_comp ..) ih

private theorem port_id (p : Port params out) : HEq (mapDataPort id p) p := by
  induction p with
  | head => exact port_head_heq (Ty.mapData_id _) (Ty.mapProfile_id _)
  | tail p ih => exact port_tail_heq (Ty.mapData_id _) (Ty.mapProfile_id _) (Ty.mapData_id _) ih

private theorem ref_heq {sort sort' : Fin n → Ty F} (hs : sort = sort') {t t' : Ty F}
    (ht : t = t') {r : Ref sort t} {r' : Ref sort' t'} (h : r.id = r'.id) : HEq r r' := by
  subst sort' t'
  obtain ⟨a, ha⟩ := r
  obtain ⟨b, hb⟩ := r'
  change a = b at h
  subst b
  rfl

private theorem composeSorts (sort : Fin n → Ty D) :
    Ty.mapData g ∘ Ty.mapData f ∘ sort = Ty.mapData (g ∘ f) ∘ sort :=
  funext fun i => Ty.mapData_comp f g (sort i)

private theorem idSorts (sort : Fin n → Ty D) : Ty.mapData id ∘ sort = sort :=
  funext fun i => Ty.mapData_id (sort i)

private theorem tuple_cons_heq {A B : Ty F → Type v} (hAB : A = B)
    {ts ts' : List (Ty F)} (hs : ts = ts') {t t' : Ty F} (ht : t = t')
    {a : A t} {b : B t'} {as : Tuple A ts} {bs : Tuple B ts'}
    (ahead : HEq a b) (tails : HEq as bs) :
    HEq (.cons a as : Tuple A (t :: ts)) (.cons b bs : Tuple B (t' :: ts')) := by
  subst B ts' t'
  cases ahead
  cases tails
  rfl

private theorem tuple_nil_heq {A B : Ty F → Type v} (hAB : A = B) :
    HEq (.nil : Tuple A []) (.nil : Tuple B []) := by subst B; rfl

private theorem refs_comp {sort : Fin n → Ty D} (args : Tuple (Ref sort) ins) :
    HEq (mapDataTuple g (fun _ => Ref.mapData g) (mapDataTuple f (fun _ => Ref.mapData f) args))
      (mapDataTuple (g ∘ f) (fun _ => Ref.mapData (g ∘ f)) args) := by
  have families := congrArg (fun s t => @Ref F n s t) (composeSorts (f := f) (g := g) sort)
  induction args with
  | nil => exact tuple_nil_heq families
  | cons h hs ih =>
    exact tuple_cons_heq families (Ty.mapProfile_comp ..) (Ty.mapData_comp ..)
      (ref_heq (composeSorts sort) (Ty.mapData_comp ..) rfl) ih

private theorem refs_id {sort : Fin n → Ty D} (args : Tuple (Ref sort) ins) :
    HEq (mapDataTuple id (fun _ => Ref.mapData id) args) args := by
  have families := congrArg (fun s t => @Ref D n s t) (idSorts sort)
  induction args with
  | nil => exact tuple_nil_heq families
  | cons h hs ih =>
    exact tuple_cons_heq families (Ty.mapProfile_id _) (Ty.mapData_id _)
      (ref_heq (idSorts sort) (Ty.mapData_id _) rfl) ih

private theorem opcode_comp (p : ProfileMap f P Q) (q : ProfileMap g Q R) (x : P ins out) :
    HEq (q (p x)) (ProfileMap.comp p q x) :=
  (cast_heq _ _).symm

private theorem opcode_fixed {Q : InstructionSet.{u,v'} D} (p : InstructionMap P Q) (x : P ins out) :
    HEq (ProfileMap.fixed (P := P) (Q := Q) p x) (p x) :=
  cast_heq _ _

private theorem label_param_heq {params params' : List (Ty F)} {t t' : Ty F}
    {p : Port params t} {p' : Port params' t'} (hp : params = params') (ht : t = t')
    (h : HEq p p') : HEq (Label.param (P := R) (Loop := L) p) (Label.param (P := R) (Loop := L) p') := by
  subst params' t'
  cases h
  rfl

private theorem label_op_heq {params params' ins ins' : List (Ty F)} {t t' : Ty F}
    {x : R ins t} {y : R ins' t'} (hp : params = params') (hi : ins = ins') (ht : t = t')
    (h : HEq x y) :
    HEq (Label.op (params := params) (Loop := L) x) (Label.op (params := params') (Loop := L) y) := by
  subst params' ins' t'
  cases h
  rfl

private theorem label_comp (p : ProfileMap f P Q) (q : ProfileMap g Q R)
    (label : Label P params L ins out) :
    HEq ((label.mapData p).mapData q) (label.mapData (ProfileMap.comp p q)) := by
  have hp := Ty.mapProfile_comp f g params
  cases label with
  | param slot => exact label_param_heq hp (Ty.mapData_comp ..) (port_comp slot)
  | op x => exact label_op_heq hp (Ty.mapProfile_comp ..) (Ty.mapData_comp ..) (opcode_comp p q x)
  | phi | theta _ | eval _ =>
    have ht := Ty.mapData_comp f g out
    simp only [Label.mapData]
    congr 1
  | pass _ =>
    simp only [Label.mapData]
    congr 1

private theorem label_fixed {Q : InstructionSet.{u,v'} D} (p : InstructionMap P Q)
    (label : Label P params L ins out) :
    HEq (label.mapData (ProfileMap.fixed (P := P) (Q := Q) p)) (label.map p id) := by
  have hp := Ty.mapProfile_id params
  cases label with
  | param slot => exact label_param_heq hp (Ty.mapData_id _) (port_id slot)
  | op x =>
    apply label_op_heq hp (Ty.mapProfile_id _) (Ty.mapData_id _)
    exact cast_heq _ _
  | phi | theta _ | eval _ =>
    have ht := Ty.mapData_id out
    simp only [Label.mapData, Label.map, id]
    congr 1
  | pass _ =>
    simp only [Label.mapData, Label.map, id]
    congr 1

private theorem node_heq {params params' : List (Ty F)} {sort sort' : Fin n → Ty F}
    {t t' : Ty F} (hp : params = params') (hs : sort = sort') (ht : t = t')
    {a : Node R params L sort t} {b : Node R params' L sort' t'}
    (hi : a.inputs = b.inputs) (hl : HEq a.label b.label) (ha : HEq a.args b.args) : HEq a b := by
  subst params' sort' t'
  obtain ⟨ai, al, aa⟩ := a
  obtain ⟨bi, bl, ba⟩ := b
  change ai = bi at hi
  subst bi
  cases hl
  cases ha
  rfl

private theorem graph_heq {params params' results results' : List (Ty F)}
    (hp : params = params') (hr : results = results')
    {a : Graph R params results n l} {b : Graph R params' results' n l}
    (hf : a.forest = b.forest) (hs : a.sort = b.sort) (hn : ∀ i, HEq (a.node i) (b.node i))
    (ho : HEq a.roots b.roots) : HEq a b := by
  subst params' results'
  obtain ⟨af, as, an, ar⟩ := a
  obtain ⟨bf, bs, bn, br⟩ := b
  change af = bf at hf
  change as = bs at hs
  subst bf bs
  have he : an = bn := funext fun i => eq_of_heq (hn i)
  subst bn
  cases ho
  rfl

theorem graph_comp (p : ProfileMap f P Q) (q : ProfileMap g Q R) (x : Graph P params results n l) :
    HEq ((x.mapData p).mapData q) (x.mapData (ProfileMap.comp p q)) := by
  refine graph_heq (Ty.mapProfile_comp ..) (Ty.mapProfile_comp ..) rfl (composeSorts x.sort) ?_ (refs_comp x.roots)
  intro i
  exact node_heq (Ty.mapProfile_comp ..) (composeSorts x.sort) (Ty.mapData_comp ..)
    (Ty.mapProfile_comp ..) (label_comp p q (x.node i).label) (refs_comp (x.node i).args)

private theorem ref_refl {sort : Fin n → Ty D} (r : Ref sort out) :
    r.reindex (Equiv.refl _) = r := by cases r; rfl

private theorem refs_refl {sort : Fin n → Ty D} (rs : Tuple (Ref sort) ins) :
    (rs.map (fun _ r => r.reindex (Equiv.refl _))) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => exact congrArg₂ Tuple.cons (ref_refl r) ih

theorem graph_fixed {Q : InstructionSet.{u,v'} D} (p : InstructionMap P Q)
    (x : Graph P params results n l) : HEq (x.mapData (ProfileMap.fixed (P := P) (Q := Q) p)) (x.mapOps p) := by
  have forest : (x.mapData (ProfileMap.fixed (P := P) (Q := Q) p)).forest = (x.mapOps p).forest := by
    change x.forest = x.forest.reindex (Equiv.refl _)
    cases x.forest with
    | mk parent =>
      congr
      funext i
      exact Option.map_id'.symm
  refine graph_heq (Ty.mapProfile_id _) (Ty.mapProfile_id _) forest (idSorts x.sort) ?_ ?_
  · intro i
    exact node_heq (Ty.mapProfile_id _) (idSorts x.sort) (Ty.mapData_id _) (Ty.mapProfile_id _)
      (label_fixed p (x.node i).label) ((refs_id (x.node i).args).trans (heq_of_eq (refs_refl _).symm))
  · exact (refs_id x.roots).trans (heq_of_eq (refs_refl _).symm)

private theorem value_forward (carrier : E → Type w) (t : Ty D)
    (x : t.Value (carrier ∘ f)) : HEq (Ty.valueMapEquiv f carrier t x) x := by
  cases t <;> rfl

private theorem value_back (carrier : E → Type w) (t : Ty D)
    (x : Option ((t.mapData f).Value carrier)) :
    HEq (x.map (Ty.valueMapEquiv f carrier t).symm) x := by
  cases t <;> cases x <;> rfl

private theorem args_comp (carrier : F → Type w)
    (xs : Tuple (Ty.Value ((carrier ∘ g) ∘ f)) ins) :
    HEq (mapDataTuple g (Ty.valueMapEquiv g carrier ·)
      (mapDataTuple f (Ty.valueMapEquiv f (carrier ∘ g) ·) xs))
      (mapDataTuple (g ∘ f) (Ty.valueMapEquiv (g ∘ f) carrier ·) xs) := by
  induction xs with
  | nil => rfl
  | @cons t ts x xs ih =>
    exact tuple_cons_heq rfl (Ty.mapProfile_comp ..) (Ty.mapData_comp ..)
      ((value_forward carrier (t.mapData f) _).trans
        ((value_forward (carrier ∘ g) t x).trans (value_forward carrier t x).symm)) ih

private theorem args_id (carrier : D → Type w) (xs : Tuple (Ty.Value carrier) ins) :
    HEq (mapDataTuple id (Ty.valueMapEquiv id carrier ·) xs) xs := by
  induction xs with
  | nil => rfl
  | @cons t ts x xs ih =>
    exact tuple_cons_heq rfl (Ty.mapProfile_id _) (Ty.mapData_id _) (value_forward carrier t x) ih

private theorem run_heq (m : Interpretation.{u'',v'',w} R)
    {ts ts' : List (Ty F)} {t t' : Ty F} (hi : ts = ts') (ht : t = t')
    {a : R ts t} {b : R ts' t'} {xs : Tuple m.Value ts} {ys : Tuple m.Value ts'}
    (h : HEq a b) (ha : HEq xs ys) : HEq (m.run a xs) (m.run b ys) := by
  subst ts' t'
  cases h
  cases ha
  rfl

theorem reduct_comp (p : ProfileMap f P Q) (q : ProfileMap g Q R)
    (m : Interpretation.{u'',v'',w} R) :
    m.reductData (ProfileMap.comp p q) = (m.reductData q).reductData p := by
  let carrier := m.carrier ∘ (g ∘ f)
  apply congrArg (fun (run : ∀ (ts : List (Ty D)) (t : Ty D), P ts t →
      Tuple (Ty.Value carrier) ts → Option (t.Value carrier)) =>
    Interpretation.mk (P := P) carrier (fun {ts t} => run ts t))
  funext ts t a xs
  apply eq_of_heq
  let direct := m.run (ProfileMap.comp p q a) (mapDataTuple (g ∘ f) (Ty.valueMapEquiv (g ∘ f) m.carrier ·) xs)
  let nested := m.run (q (p a)) (mapDataTuple g (Ty.valueMapEquiv g m.carrier ·)
    (mapDataTuple f (Ty.valueMapEquiv f (m.carrier ∘ g) ·) xs))
  change HEq (direct.map (Ty.valueMapEquiv (g ∘ f) m.carrier t).symm)
    ((nested.map (Ty.valueMapEquiv g m.carrier (t.mapData f)).symm).map
      (Ty.valueMapEquiv f (m.carrier ∘ g) t).symm)
  exact (value_back m.carrier t direct).trans
    ((run_heq m (Ty.mapProfile_comp f g ts).symm (Ty.mapData_comp f g t).symm
        (opcode_comp p q a).symm (args_comp (f := f) (g := g) m.carrier xs).symm).trans
      ((value_back (m.carrier ∘ g) t _).trans (value_back m.carrier (t.mapData f) nested)).symm)

theorem reduct_fixed {Q : InstructionSet.{u,v'} D} (p : InstructionMap P Q)
    (m : Interpretation.{u,v',w} Q) :
    m.reductData (ProfileMap.fixed (P := P) (Q := Q) p) = m.reduct p := by
  apply congrArg (fun (run : ∀ (ts : List (Ty D)) (t : Ty D), P ts t →
      Tuple (Ty.Value m.carrier) ts → Option (t.Value m.carrier)) =>
    Interpretation.mk (P := P) m.carrier (fun {ts t} => run ts t))
  funext ts t a xs
  apply eq_of_heq
  let mapped := m.run (ProfileMap.fixed (P := P) (Q := Q) p a)
    (mapDataTuple id (Ty.valueMapEquiv id m.carrier ·) xs)
  change HEq (mapped.map (Ty.valueMapEquiv id m.carrier t).symm) (m.run (p a) xs)
  exact (value_back m.carrier t mapped).trans
    (run_heq m (Ty.mapProfile_id ts) (Ty.mapData_id t)
      (opcode_fixed (P := P) (Q := Q) (ins := ts) (out := t) p a) (args_id m.carrier xs))

end Silmaril.SSA.PEG.SortMapProofs

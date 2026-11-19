module

public import Silmaril.Semantics.Function.Defs
public import Silmaril.Semantics.Region.Abstract.Thms
import Silmaril.Proofs.Semantics.Function.Graph

@[expose] public section
namespace Silmaril.Semantics.Function
universe u
variable {sig : Signature.{u}}

theorem body_presence {model : Model sig} (closed : Region.Abstract.Closed (Laws sig) model)
    {context : sig.Context} {name : sig.Internal} {row : sig.Body}
    (body : decomposition model context name row) : Atom.node context (.localFn name) ∈ model :=
  closed _ (PresenceRule.body context name row) (Set.singleton_subset_iff.mpr body)

theorem call_presence {model : Model sig} (closed : Region.Abstract.Closed (Laws sig) model)
    {context : sig.Context} {edge : Edge sig} (call : calls model context edge) :
    Atom.node context (.localFn edge.origin.caller) ∈ model ∧ Atom.node context edge.callee ∈ model :=
  ⟨closed _ (PresenceRule.caller context edge) (Set.singleton_subset_iff.mpr call),
    closed _ (PresenceRule.callee context edge) (Set.singleton_subset_iff.mpr call)⟩

theorem foreign_leaf (edges : Calls sig) (accept : Dispatch → Prop) (leaf : sig.Foreign)
    (dest : Node sig) : ¬ (graph edges accept).edge (.foreign leaf) dest :=
  by rintro ⟨_, _, _, eq, _⟩; cases eq

theorem graph_mono {actual possible : Calls sig} (covers : MayCover actual possible)
    {accept wider : Dispatch → Prop} (mode : ∀ tag, accept tag → wider tag) :
    ∀ ⦃source dest⦄, (graph actual accept).edge source dest → (graph possible wider).edge source dest :=
  fun {_ _} ⟨edge, evidence, ok, src, dst⟩ => ⟨edge, covers evidence, mode _ ok, src, dst⟩

theorem reach_mono {actual possible : Calls sig} (covers : MayCover actual possible)
    {accept wider : Dispatch → Prop} (mode : ∀ tag, accept tag → wider tag)
    {source dest : Node sig} (path : Reachable (graph actual accept) source dest) :
    Reachable (graph possible wider) source dest :=
  Relation.ReflTransGen.mono (fun _ _ edge => graph_mono covers mode edge) source dest path

theorem path_mono {actual possible : Calls sig} (covers : MayCover actual possible)
    {accept wider : Dispatch → Prop} (mode : ∀ tag, accept tag → wider tag)
    {source dest : Node sig} (path : CallPath (graph actual accept) source dest) :
    CallPath (graph possible wider) source dest :=
  Relation.TransGen.mono (fun _ _ edge => graph_mono covers mode edge) source dest path

theorem reachable_iff_mem {α : Type u} {g : Graph.RelGraph α} {root : α} {seen : Set α}
    (cert : ReachCertificate g root seen) (dest : α) :
    Relation.ReflTransGen g.edge root dest ↔ dest ∈ seen := Proofs.reachable_iff_mem cert dest

theorem bounded_to_top {α : Type u} (bound : Option (Set α)) {target : α}
    (_ : admits bound target) : admits none target := trivial

theorem topify_covers (analysis : Analysis sig) : MayCover analysis.may analysis.topify.may :=
  Proofs.topify_covers analysis

theorem reach_problem_of_certificate {g : Graph.RelGraph (Node sig)} {root : Node sig} {seen : Set (Node sig)}
    (cert : ReachCertificate g root seen) : ReachProblem g root seen :=
  fun dest => (reachable_iff_mem cert dest).symm

end Silmaril.Semantics.Function

module

public import Silmaril.Semantics.Region.Certified.Defs

@[expose] public section
namespace Silmaril.Semantics.Region.Certified
universe u v w z
variable {Img : Type u} {Intf : Type v} {Seg : Type w} {Lab : Type z}
variable {M N O : Model (Img := Img) (Intf := Intf) (Seg := Seg) (Lab := Lab)}

theorem Refines.refl : Refines M M := fun _ h => h
theorem Refines.trans (h : Refines M N) (k : Refines N O) : Refines M O := fun _ x => k (h x)

theorem BasicBlock.transport_id {i : Img} {a : Intf} (b : BasicBlock M i a) :
    b.transport Refines.refl = b := rfl
theorem BasicBlock.transport_comp (h : Refines M N) (k : Refines N O)
    {i : Img} {a : Intf} (b : BasicBlock M i a) :
    (b.transport h).transport k = b.transport (h.trans k) := rfl

theorem WithGraph.transport_id {i : Img} {a : Intf} {G : Type*} {P : G → Prop}
    {coherent : SegmentRow Seg Lab → G → Prop} (r : WithGraph M i a G P coherent) :
    r.transport Refines.refl (fun _ h => h) = r := rfl

theorem WithGraph.transport_comp (h : Refines M N) (k : Refines N O)
    {i : Img} {a : Intf} {G : Type*} {P Q R : G → Prop}
    {coherent : SegmentRow Seg Lab → G → Prop} (pq : ∀ g, P g → Q g) (qr : ∀ g, Q g → R g)
    (r : WithGraph M i a G P coherent) :
    (r.transport h pq).transport k qr = r.transport (h.trans k) (fun g hp => qr g (pq g hp)) := rfl

theorem transport_data (h : Refines M N) {i : Img} {a : Intf} {G : Type*} {P Q : G → Prop}
    {coherent : SegmentRow Seg Lab → G → Prop} (pq : ∀ g, P g → Q g)
    (r : WithGraph M i a G P coherent) :
    (r.transport h pq).row = r.row ∧ (r.transport h pq).graph = r.graph := ⟨rfl, rfl⟩

end Silmaril.Semantics.Region.Certified

module

public import Silmaril.Containers.Http.Defs
public import Silmaril.Containers.Fixtures.Thms
public import Silmaril.Net.Http1.Message.Thms

/-!
# Proofs: containers as HTTP servers

Proofs for `Silmaril.Containers.Http.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Http

open Silmaril.Containers Silmaril.Containers.Http Silmaril.Containers.Fixtures Silmaril.Servers

theorem toSockEv_send {e : Ev} {fd : Nat} {bs : List UInt8}
    (h : toSockEv e = some (.send fd bs)) : ∃ s, e = .send s bs := by
  cases e <;> simp only [toSockEv] at h <;> (try split at h) <;> cases h
  exact ⟨_, rfl⟩

theorem sent_of_sends (r : List UInt8) (c : Platform.ConnId) :
    ∀ u : List Ev, (∀ e ∈ u, ∀ s bs, e = .send s bs → bs = r) →
      ∃ n, Platform.sent c (sockTrace u) = (List.replicate n r).flatten
  | [], _ => ⟨0, rfl⟩
  | e :: u, h => by
    obtain ⟨n, hn⟩ := sent_of_sends r c u fun e he => h e (.tail _ he)
    simp only [sockTrace, List.filterMap_cons]
    cases hx : toSockEv e with
    | none => exact ⟨n, hn⟩
    | some x =>
      cases x with
      | send fd bs =>
        obtain ⟨s, rfl⟩ := toSockEv_send hx
        have hr := h _ (.head _) s bs rfl
        subst hr
        by_cases hc : fd = c
        · refine ⟨n + 1, ?_⟩
          simp only [Platform.sent, hc, ↓reduceIte]
          rw [show sockTrace u = List.filterMap toSockEv u from rfl] at hn
          rw [hn, List.replicate_succ, List.flatten_cons]
        · refine ⟨n, ?_⟩
          simp only [Platform.sent, hc, ↓reduceIte, List.nil_append]
          exact hn
      | accept _ => exact ⟨n, hn⟩
      | recv _ _ => exact ⟨n, hn⟩
      | close _ => exact ⟨n, hn⟩

theorem http_sent (fr : Platform.Framing) {tr : List Platform.SockEv}
    (h : (platform small fr).runs http tr) (c : Platform.ConnId) :
    ∃ n, Platform.sent c tr = (List.replicate n okResponse).flatten := by
  obtain ⟨b, u, hb, hu, rfl⟩ := h
  exact sent_of_sends okResponse c u fun e he s bs hs =>
    Fixtures.http_sends_only b hb u hu e he s bs hs

theorem okResponse_parses :
    Silmaril.Net.Http1.parseResponseHead ⟨okResponse.toArray⟩ =
      .ok Fixtures.okHead (Silmaril.Net.Http1.encResponseHead Fixtures.okHead).length := by
  have he : okResponse = Silmaril.Net.Http1.encResponseHead Fixtures.okHead ++ ascii "ok" := by
    decide
  rw [he]
  exact Silmaril.Net.Http1.parseResponseHead_encode (by decide +kernel) _

end Silmaril.Proofs.Containers.Http

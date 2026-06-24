

open Topology

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A := by
  intro h
  dsimp [P2, P1] at h ⊢
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'
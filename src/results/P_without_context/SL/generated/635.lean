

open Topology
open Set

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3] at *
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact h_subset hx'
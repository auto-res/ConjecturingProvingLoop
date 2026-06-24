

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P1 A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'
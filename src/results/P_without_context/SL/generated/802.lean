

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro h x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  exact interior_subset hx'
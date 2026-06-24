

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2 x hx
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
  exact interior_subset hx_in
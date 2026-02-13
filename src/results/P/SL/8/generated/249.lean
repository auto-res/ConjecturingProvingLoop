

theorem P2_interior_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (interior A)) ↔ Topology.P2 (interior A) := by
  simpa [interior_interior]


theorem P1_interior_interior_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (interior A)) ↔ Topology.P1 (interior A) := by
  simpa [interior_interior]
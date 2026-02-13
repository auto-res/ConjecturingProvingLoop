

theorem Topology.P1_iff_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X:=X) A ↔ A ⊆ closure (interior A) := by
  rfl
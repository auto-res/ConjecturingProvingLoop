

theorem Topology.P2_iff_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (X := X) A ↔ A ⊆ interior (closure (interior A)) := by
  rfl
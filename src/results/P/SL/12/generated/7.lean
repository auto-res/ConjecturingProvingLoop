

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (X := X) (interior A) := by
  dsimp [Topology.P3]
  have h : interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (Topology.interior_subset_interior_closure (X := X) (A := interior A))
  exact h
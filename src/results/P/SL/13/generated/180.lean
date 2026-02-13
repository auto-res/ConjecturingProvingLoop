

theorem Topology.interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B) := by
  simpa [Set.union_comm] using
    (Topology.interior_subset_interior_union_left (X := X) (A := B) (B := A))
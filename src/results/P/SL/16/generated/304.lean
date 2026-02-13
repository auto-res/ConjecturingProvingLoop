

theorem Topology.interior_closure_subset_interior_closure_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure B) ⊆ interior (closure (A ∪ B)) := by
  simpa [Set.union_comm] using
    (Topology.interior_closure_subset_interior_closure_union_left
      (X := X) (A := B) (B := A))
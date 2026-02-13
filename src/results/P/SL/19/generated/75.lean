

theorem Topology.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ∪ interior B ⊆ interior (A ∪ B) := by
  exact
    Topology.interior_union_subset_interior_union
      (X := X) (A := A) (B := B)
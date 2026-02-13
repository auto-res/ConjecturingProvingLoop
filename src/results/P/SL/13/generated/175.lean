

theorem Topology.interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ∪ interior B ⊆ interior (A ∪ B) := by
  simpa using
    (Topology.union_interior_subset_interior_union (X := X) (A := A) (B := B))
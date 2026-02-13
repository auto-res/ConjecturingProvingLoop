

theorem Topology.union_interior_eq_self
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    ((A : Set X) ∪ interior A) = A := by
  simpa using
    (Set.union_eq_left.2
      (interior_subset : (interior A : Set X) ⊆ A))
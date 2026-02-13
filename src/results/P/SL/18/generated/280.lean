

theorem closure_union_eq_univ_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDense : Dense (B : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  simpa [Set.union_comm] using
    (Topology.closure_union_eq_univ_of_dense_left (A := B) (B := A) hDense)
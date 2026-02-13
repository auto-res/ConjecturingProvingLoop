

theorem Topology.closure_interior_union_eq_univ_of_dense_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h_dense : closure (interior B) = (Set.univ : Set X)) :
    closure (interior (A ∪ B)) = (Set.univ : Set X) := by
  simpa [Set.union_comm] using
    (Topology.closure_interior_union_eq_univ_of_dense_left
      (X := X) (A := B) (B := A) h_dense)
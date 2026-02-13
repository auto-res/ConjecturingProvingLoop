

theorem closure_union_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) (hDenseB : Dense (B : Set X)) :
    closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  -- Use the existing lemma for the left factor.
  have _ :=
    Topology.closure_union_eq_univ_of_dense_right (A := A) (B := B) hDenseB
  exact
    Topology.closure_union_eq_univ_of_dense_left (A := A) (B := B) hDenseA
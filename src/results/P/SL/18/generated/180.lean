

theorem dense_union_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hDenseA : Dense (A : Set X)) :
    Dense (A ∪ B : Set X) := by
  -- Via the existing lemma, the closure of the union is the whole space.
  have hClosUnion :
      closure (A ∪ B : Set X) = (Set.univ : Set X) :=
    Topology.closure_union_eq_univ_of_dense_left
      (A := A) (B := B) hDenseA
  -- Translate the closure equality back into density.
  exact
    (Topology.dense_iff_closure_eq_univ (A := A ∪ B)).2 hClosUnion
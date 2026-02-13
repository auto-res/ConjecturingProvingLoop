

theorem closure_union_eq_univ_of_dense_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (B : Set X) = (Set.univ : Set X) →
      closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
  intro hB
  have h := closure_union_eq_univ_of_dense_left (A := B) (B := A) hB
  simpa [Set.union_comm] using h
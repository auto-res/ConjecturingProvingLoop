

theorem closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : closure (A : Set X) = (Set.univ : Set X)) :
    closure ((A ∪ B) : Set X) = (Set.univ : Set X) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hA, Set.union_univ, Set.univ_union] using h
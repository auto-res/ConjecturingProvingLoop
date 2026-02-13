

theorem closure_union_eq_union_closure_left_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed (A : Set X)) :
    closure ((A ∪ B) : Set X) = A ∪ closure (B : Set X) := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hA.closure_eq] using h
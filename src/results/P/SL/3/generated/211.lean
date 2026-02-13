

theorem closure_union_eq_union_closure_right_of_isClosed {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsClosed (B : Set X)) :
    closure ((A ∪ B) : Set X) = closure (A : Set X) ∪ B := by
  have h := closure_union_eq_union_closure (A := A) (B := B)
  simpa [hB.closure_eq] using h


theorem closure_union_closed_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) :
    closure (A ∪ B) = closure A ∪ B := by
  have h := closure_union (s := A) (t := B)
  simpa [hB.closure_eq] using h
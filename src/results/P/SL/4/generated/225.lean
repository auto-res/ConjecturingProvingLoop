

theorem closure_union_closed_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) :
    closure (A ∪ B) = A ∪ closure B := by
  have h := closure_union (s := A) (t := B)
  simpa [hA.closure_eq] using h
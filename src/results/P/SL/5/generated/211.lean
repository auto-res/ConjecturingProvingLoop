

theorem closure_union_interior_left {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ B : Set X) = closure (interior A) ∪ closure B := by
  simpa using closure_union (interior A) B


theorem closure_union_interior_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ interior B : Set X) = closure A ∪ closure (interior B) := by
  simpa using closure_union (A : Set X) (interior B)
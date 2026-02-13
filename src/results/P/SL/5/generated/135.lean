

theorem closure_union_interior_eq {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ interior B) =
      closure (interior A) ∪ closure (interior B) := by
  simpa using closure_union (interior (A : Set X)) (interior B)
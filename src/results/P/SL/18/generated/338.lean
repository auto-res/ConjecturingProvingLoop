

theorem closure_interior_union_eq_union_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∪ B) =
      closure (interior (A : Set X)) ∪ closure B := by
  simpa [closure_union]


theorem interior_closure_union_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A ∪ closure B) = interior (closure (A ∪ B)) := by
  simpa [closure_union]
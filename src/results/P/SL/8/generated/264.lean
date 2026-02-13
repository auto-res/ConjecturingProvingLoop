

theorem interior_closure_union_eq_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∪ B)) = interior (closure A ∪ closure B) := by
  simpa [closure_union]
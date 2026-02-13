

theorem interior_closure_union_eq
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (closure ((A ∪ B) : Set X)) =
      interior (closure (A : Set X) ∪ closure B) := by
  simpa [closure_union]
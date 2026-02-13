

theorem closure_interior_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    closure (interior (∅ : Set X)) = (∅ : Set X) := by
  simpa [interior_empty] using (closure_empty : closure (∅ : Set X) = ∅)
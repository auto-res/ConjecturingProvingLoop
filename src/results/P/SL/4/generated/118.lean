

theorem interior_closure_empty_eq_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (∅ : Set X)) = (∅ : Set X) := by
  simp [closure_empty]
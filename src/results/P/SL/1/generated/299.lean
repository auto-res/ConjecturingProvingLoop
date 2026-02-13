

theorem interior_closure_interior_empty {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (∅ : Set X))) = (∅ : Set X) := by
  simp


theorem closure_interior_inter_eq_closure_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  simpa [interior_inter]
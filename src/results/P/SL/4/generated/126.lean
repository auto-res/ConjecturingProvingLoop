

theorem closure_interior_inter_eq_closure_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) = closure (interior (A ∩ B)) := by
  simpa [interior_inter]


theorem closure_interior_comp
    {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => closure (interior A)) ∘
        (fun A : Set X => closure (interior A))) =
      (fun A : Set X => closure (interior A)) := by
  funext A
  simp [Function.comp,
    Topology.closure_interior_closure_interior_eq_closure_interior (A := A)]
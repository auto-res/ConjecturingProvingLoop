

theorem interior_closure_comp {X : Type*} [TopologicalSpace X] :
    ((fun A : Set X => interior (closure A)) ∘
        (fun A : Set X => interior (closure A))) =
      (fun A : Set X => interior (closure A)) := by
  funext A
  simp [Function.comp,
    Topology.interior_closure_interior_closure_eq_interior_closure]
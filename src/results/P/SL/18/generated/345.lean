

theorem closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h₁ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure
        (A := interior A))
  have h₂ :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := A))
  simpa [h₁, h₂]
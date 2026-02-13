

theorem closure_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  -- From `interior_closure_interior_closure`, the two interiors coincide.
  have h := Topology.interior_closure_interior_closure (A := A)
  simpa [h]
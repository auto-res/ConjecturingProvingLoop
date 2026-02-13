

theorem Topology.interior_closure_interior_closure_interior_eq_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  -- Use the existing equality of closures and apply `interior` to both sides.
  have h :=
    (Topology.closure_interior_closure_interior_eq_closure_interior
      (A := A))
  simpa using congrArg (fun S : Set X => interior S) h
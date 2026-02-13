

theorem Topology.closure_interior_closure_interior_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  have h :=
    Topology.interior_closure_interior_closure_eq_interior_closure (A := A)
  simpa using congrArg closure h
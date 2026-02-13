

theorem Topology.interior_closure_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure A)) = interior (closure A) := by
  simpa using
    congrArg (fun S : Set X => interior S) (closure_closure : closure (closure A) = closure A)
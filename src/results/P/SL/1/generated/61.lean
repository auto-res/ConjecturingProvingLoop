

theorem Topology.interior_closure_eq_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have hcl : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P2 (A := A) hP2
  simpa using congrArg (fun S : Set X => interior S) hcl
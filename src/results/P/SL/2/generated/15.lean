

theorem Topology.P2_implies_interior_closure_interior_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure (interior A)) = interior (closure A) := by
  intro hP2
  have h := Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  simpa using congrArg interior h
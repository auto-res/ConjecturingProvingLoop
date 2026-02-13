

theorem Topology.P3_implies_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      interior (closure (interior (closure A))) = interior (closure A) := by
  intro hP3
  have h :=
    Topology.P3_implies_closure_interior_closure_eq_closure (A := A) hP3
  simpa using congrArg interior h
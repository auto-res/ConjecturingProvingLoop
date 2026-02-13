

theorem Topology.P1_implies_interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure (interior (closure (A : Set X)))) =
        interior (closure A) := by
  intro hP1
  have h :=
    Topology.P1_implies_closure_interior_closure_eq_closure (A := A) hP1
  simpa using congrArg interior h
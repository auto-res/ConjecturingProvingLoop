

theorem Topology.P1_implies_closure_interior_closure_eq_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure A := by
  intro hP1
  -- `closure A` itself satisfies `P1`
  have hP1_closure : Topology.P1 (closure A) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Apply the known equality for `P1 (closure A)`
  have hEq :=
    Topology.P1_implies_closure_interior_eq_closure (A := closure A) hP1_closure
  simpa [closure_closure] using hEq
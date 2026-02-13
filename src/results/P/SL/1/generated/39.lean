

theorem Topology.P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  have hEq : closure A = closure (interior (closure A)) :=
    Topology.closure_eq_closure_interior_closure_of_P3 (A := A) hP3
  have hP1 : Topology.P1 (closure A) :=
    Topology.P1_of_closure_eq_closure_interior
      (A := closure A)
      (by
        simpa [closure_closure] using hEq)
  exact hP1


theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  have h_eq : closure (closure A) = closure (interior (closure A)) := by
    calc
      closure (closure A) = closure A := by
        simpa [closure_closure]
      _ = closure (interior (closure A)) := by
        simpa using
          (Topology.closure_eq_closure_interior_closure_of_P3
            (X := X) (A := A) hP3)
  exact
    (Topology.P1_iff_closure_eq_closure_interior
        (X := X) (A := closure A)).2 h_eq
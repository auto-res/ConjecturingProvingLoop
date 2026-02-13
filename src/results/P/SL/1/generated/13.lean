

theorem P3_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior (closure A)) := by
  simpa using (P3_interior (A := closure A))
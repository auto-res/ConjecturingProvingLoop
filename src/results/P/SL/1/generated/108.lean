

theorem Topology.P3_closure_closure_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  have hEq : closure (closure A) = closure A := closure_closure
  constructor
  · intro hP3
    simpa [hEq] using hP3
  · intro hP3
    simpa [hEq] using hP3
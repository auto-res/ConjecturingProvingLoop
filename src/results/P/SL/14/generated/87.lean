

theorem Topology.P1_closure_iff_closureInterior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure A)) = closure A := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P1_iff_closureInterior_eq_of_isClosed
      (X := X) (A := closure A) hClosed)
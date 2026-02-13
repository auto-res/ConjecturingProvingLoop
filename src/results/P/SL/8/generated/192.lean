

theorem P2_closure_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (closure A)) :
    Topology.P1 (closure A) := by
  simpa [closure_closure] using
    (Topology.P2_imp_P1_closure (X := X) (A := closure A)) hP2
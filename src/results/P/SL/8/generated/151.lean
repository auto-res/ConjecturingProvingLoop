

theorem isOpen_closure_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P2 (closure A) := by
  simpa using
    Topology.isOpen_imp_P2 (X := X) (A := closure A) h_open
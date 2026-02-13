

theorem isOpen_closure_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_open : IsOpen (closure A)) :
    Topology.P1 (closure A) := by
  simpa using
    Topology.isOpen_imp_P1 (X := X) (A := closure A) h_open
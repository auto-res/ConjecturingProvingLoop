

theorem P1_closure_of_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hOpen
  simpa [closure_closure] using
    (Topology.isOpen_implies_P1_closure
        (X := X) (A := closure (A : Set X))) hOpen


theorem P3_closure_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (closure A)) :
    IsOpen (closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  exact
    Topology.closed_P3_isOpen (X := X) (A := closure A) h_closed hP3
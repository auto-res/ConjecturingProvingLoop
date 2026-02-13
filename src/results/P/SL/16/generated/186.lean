

theorem Topology.P3_closure_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P3 (X := X) (closure A) := by
  exact (Topology.P3_closure_iff_open_closure (X := X) (A := A)).2 hOpen
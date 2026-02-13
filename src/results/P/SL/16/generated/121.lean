

theorem Topology.P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) : Topology.P2 (X := X) (closure A) := by
  exact (Topology.P2_closure_iff_open_closure (X := X) (A := A)).2 hOpen


theorem Topology.P1_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) : Topology.P1 (closure (A : Set X)) := by
  have hTriple := Topology.IsOpen_P1_P2_P3_closure (A := A) hOpen
  exact hTriple.1


theorem Topology.P1_closure_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) (closure A) := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.isOpen_P1 (X := X) (A := A) hA
  exact Topology.P1_closure_of_P1 (X := X) (A := A) hP1
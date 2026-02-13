

theorem Topology.closure_has_P1_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_implies_P1 (X := X) (A := A) hA
  exact Topology.closure_has_P1_of_P1 (X := X) (A := A) hP1A
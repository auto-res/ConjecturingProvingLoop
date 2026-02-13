

theorem isOpen_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 (closure A) := by
  have hP1A : Topology.P1 A :=
    Topology.isOpen_P1 (A := A) hA
  exact Topology.P1_imp_P1_closure (A := A) hP1A
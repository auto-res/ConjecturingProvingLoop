

theorem isOpen_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen A) :
    Topology.P1 (closure A) := by
  -- From openness we get `P2 A`
  have hP2 : Topology.P2 A :=
    Topology.isOpen_imp_P2 (X := X) (A := A) hA_open
  -- And `P2 A` implies `P1 (closure A)`
  exact Topology.P2_imp_P1_closure (X := X) (A := A) hP2
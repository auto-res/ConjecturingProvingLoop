

theorem closed_P3_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A := by
  -- First, a closed set satisfying `P3` is open.
  have hA_open : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  -- Openness implies `P1`.
  exact Topology.isOpen_imp_P1 (X := X) (A := A) hA_open
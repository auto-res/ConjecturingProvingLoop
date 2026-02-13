

theorem P2_closed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  -- Translate `P2` for a closed set into openness.
  have hOpen : IsOpen A :=
    (Topology.P2_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP2
  -- Open sets satisfy `P1`.
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen
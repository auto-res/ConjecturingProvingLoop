

theorem Topology.closed_P123_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) ↔
      IsOpen A := by
  constructor
  · rintro ⟨_, _, hP3⟩
    exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  · intro hOpen
    exact
      Topology.isOpen_satisfies_P1_P2_P3 (X := X) (A := A) hOpen



theorem Topology.P2_iff_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · intro hP3
    dsimp [Topology.P2, Topology.P3] at hP3 ⊢
    simpa [hA.interior_eq] using hP3
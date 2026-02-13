

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 (A := A) ↔ Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3]
  simpa [hA.interior_eq]
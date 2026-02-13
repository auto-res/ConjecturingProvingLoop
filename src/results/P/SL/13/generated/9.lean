

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  dsimp [Topology.P2, Topology.P3]
  have h_eq : interior (closure (interior A)) = interior (closure A) := by
    simpa [hA.interior_eq]
  simpa [h_eq]
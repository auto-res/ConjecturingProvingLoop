

theorem Topology.P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  dsimp [Topology.P2, Topology.P3]
  have h_int : interior A = A := hA.interior_eq
  simpa [h_int] using
    (Iff.rfl :
      (A ⊆ interior (closure (interior A))) ↔
      (A ⊆ interior (closure (interior A))))
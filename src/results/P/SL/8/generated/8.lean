

theorem isOpen_imp_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A := by
  dsimp [Topology.P2]
  have hP3 := (Topology.isOpen_imp_P3 (X := X) (A := A) hA)
  dsimp [Topology.P3] at hP3
  simpa [hA.interior_eq] using hP3
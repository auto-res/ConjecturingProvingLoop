

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · exact Topology.P2_implies_P3 (X := X) (A := A)
  · intro hP3
    dsimp [Topology.P2]
    dsimp [Topology.P3] at hP3
    intro x hxA
    have hx_int : x ∈ interior (closure A) := hP3 hxA
    simpa [hA.interior_eq] using hx_int
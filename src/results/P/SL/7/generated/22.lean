

theorem Topology.P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 hP2
  · intro hP3
    dsimp [Topology.P2]
    dsimp [Topology.P3] at hP3
    intro x hx
    have hx' : x ∈ interior (closure A) := hP3 hx
    have hEq : interior (closure (interior A)) = interior (closure A) := by
      simpa [hInt]
    simpa [hEq] using hx'
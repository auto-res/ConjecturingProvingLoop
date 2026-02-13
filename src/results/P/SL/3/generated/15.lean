

theorem Topology.P3_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    dsimp [Topology.P3, Topology.P2] at hP3 ⊢
    intro x hx
    have : (x : X) ∈ interior (closure A) := hP3 hx
    simpa [hA.interior_eq] using this
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2
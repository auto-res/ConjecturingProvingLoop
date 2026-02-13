

theorem Topology.isOpen_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hOpen
  constructor
  · intro hP2
    exact Topology.P2_implies_P3 (A := A) hP2
  · intro hP3
    intro x hxA
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [hOpen.interior_eq] using hx
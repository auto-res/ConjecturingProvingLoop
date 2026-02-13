

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  have hInt : interior (A : Set X) = A := hA.interior_eq
  constructor
  · intro hP2
    dsimp [Topology.P3]
    intro x hxA
    have hx : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [hInt] using hx
  · intro hP3
    dsimp [Topology.P2]
    intro x hxA
    have hx : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [hInt] using hx
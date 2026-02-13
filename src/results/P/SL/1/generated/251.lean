

theorem Topology.P2_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · rintro ⟨hP2, _⟩
    exact (Topology.P2_iff_isOpen_of_isClosed (A := A) hA).1 hP2
  · intro hOpen
    exact And.intro
      (Topology.P2_of_isOpen (A := A) hOpen)
      (Topology.P3_of_isOpen (A := A) hOpen)
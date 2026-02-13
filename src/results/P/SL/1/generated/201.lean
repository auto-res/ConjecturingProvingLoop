

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · rintro ⟨_, _, hP3⟩
    exact (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  · intro hOpen
    exact
      And.intro
        (Topology.P1_of_isOpen (A := A) hOpen)
        (And.intro
          (Topology.P2_of_isOpen (A := A) hOpen)
          (Topology.P3_of_isOpen (A := A) hOpen))
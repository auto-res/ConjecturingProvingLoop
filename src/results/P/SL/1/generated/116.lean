

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen A := by
  -- `P3 A` is equivalent to `IsOpen A` for closed sets.
  have hP3 : Topology.P3 A ↔ IsOpen A :=
    Topology.P3_iff_isOpen_of_isClosed (A := A) hA
  -- Establish the desired equivalence.
  constructor
  · rintro ⟨_, hPA3⟩
    -- From the second component obtain openness.
    exact hP3.1 hPA3
  · intro hOpen
    -- Openness yields both `P1` and `P3`.
    exact
      And.intro
        (Topology.P1_of_isOpen (A := A) hOpen)
        (Topology.P3_of_isOpen (A := A) hOpen)
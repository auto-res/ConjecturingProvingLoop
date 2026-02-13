

theorem Topology.P1_and_P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A) ↔ IsOpen A := by
  -- Existing equivalence between `P2` and openness for closed sets.
  have hEq : Topology.P2 A ↔ IsOpen A :=
    Topology.P2_iff_isOpen_of_isClosed (A := A) hA
  -- Prove each direction.
  constructor
  · rintro ⟨_, hP2⟩
    exact hEq.mp hP2
  · intro hOpen
    exact And.intro
      (Topology.P1_of_isOpen (A := A) hOpen)
      (hEq.mpr hOpen)
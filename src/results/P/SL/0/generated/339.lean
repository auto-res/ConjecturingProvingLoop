

theorem P2_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  -- Equivalences of `P2` and `P3` with openness for a closed set.
  have hP2 : Topology.P2 A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA
  have hP3 : Topology.P3 A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA
  -- Assemble the desired equivalence.
  constructor
  · rintro ⟨hP2A, _⟩
    exact (hP2).1 hP2A
  · intro hOpen
    have hAll := Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen
    exact And.intro hAll.2.1 hAll.2.2
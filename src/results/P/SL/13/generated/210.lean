

theorem Topology.P2_iff_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) :
    Topology.P2 (X:=X) A ↔ Topology.P1 (X:=X) A := by
  -- Start from the general equivalence `P2 ↔ P1 ∧ P3`.
  have h := Topology.P2_iff_P1_and_P3 (X := X) (A := A)
  -- Since `hP3` is assumed, `P1 ∧ P3` is equivalent to `P1`.
  have h_aux :
      (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) ↔
        Topology.P1 (X:=X) A := by
    constructor
    · intro h'
      exact h'.1
    · intro hP1
      exact And.intro hP1 hP3
  -- Combine the two equivalences.
  simpa using h.trans h_aux
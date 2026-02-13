

theorem Topology.P2_iff_P3_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X:=X) A) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  -- Start from the general equivalence `P2 ↔ P1 ∧ P3`.
  have h := Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)
  -- Given `hP1`, the conjunction `P1 ∧ P3` is equivalent to `P3`.
  have h_aux :
      (Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A) ↔
        Topology.P3 (X:=X) A := by
    constructor
    · intro h'
      exact h'.2
    · intro hP3
      exact And.intro hP1 hP3
  -- Combine the two equivalences.
  simpa using h.trans h_aux
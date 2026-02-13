

theorem P2_and_isClosed_iff_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed (A : Set X)) :
    (Topology.P2 A ∧ IsClosed (A : Set X)) ↔
      (Topology.P3 A ∧ IsClosed (A : Set X)) := by
  -- Equivalence between `P2` and `P3` for closed sets.
  have hEquiv :=
    Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed
  constructor
  · rintro ⟨hP2, hC⟩
    have hP3 : Topology.P3 A := hEquiv.1 hP2
    exact And.intro hP3 hC
  · rintro ⟨hP3, hC⟩
    have hP2 : Topology.P2 A := hEquiv.2 hP3
    exact And.intro hP2 hC
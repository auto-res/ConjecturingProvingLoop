

theorem Topology.P1_iff_P3_compl_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 (Aᶜ) ↔ Topology.P3 (Aᶜ) := by
  have h₁ := Topology.P1_iff_P2_compl_of_isClosed (X := X) (A := A) hA_closed
  have h₂ := Topology.P2_iff_P3_compl_of_isClosed (X := X) (A := A) hA_closed
  simpa using h₁.trans h₂
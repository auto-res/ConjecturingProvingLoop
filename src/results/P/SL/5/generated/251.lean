

theorem P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P3 (X := X) A := by
  have h₁ := Topology.P1_iff_P2_of_dense_interior (X := X) (A := A) h
  have h₂ := (Topology.P3_iff_P2_of_dense_interior (X := X) (A := A) h).symm
  exact h₁.trans h₂
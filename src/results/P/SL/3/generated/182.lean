

theorem Topology.P1_iff_P3_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h_dense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ := Topology.P1_iff_P2_of_dense_interior (A := A) h_dense
  have h₂ := Topology.P3_iff_P2_of_dense_interior (A := A) h_dense
  simpa using h₁.trans h₂.symm
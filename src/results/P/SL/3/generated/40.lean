

theorem P1_interior_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have h₁ := Topology.P1_interior_iff_P2_interior (A := A)
  have h₂ := Topology.P3_interior_iff_P2_interior (A := A)
  simpa using h₁.trans h₂.symm
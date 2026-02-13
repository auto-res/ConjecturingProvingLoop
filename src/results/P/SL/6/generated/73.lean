

theorem P1_iff_P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P2 (interior A) := by
  have h₁ := (Topology.P1_iff_P3_of_interior (A := A))
  have h₂ := (Topology.P3_iff_P2_of_interior (A := A))
  exact h₁.trans h₂
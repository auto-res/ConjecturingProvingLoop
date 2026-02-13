

theorem P1_iff_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have h₁ :
      Topology.P1 (interior (A : Set X)) ↔
        Topology.P2 (interior (A : Set X)) :=
    (Topology.P1_iff_P2_of_interior (X := X) (A := A))
  have h₂ :
      Topology.P2 (interior (A : Set X)) ↔
        Topology.P3 (interior (A : Set X)) :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  exact h₁.trans h₂
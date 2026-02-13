

theorem P1_iff_P3_of_clopen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClopen : IsClopen (A : Set X)) :
    Topology.P1 A ↔ Topology.P3 A := by
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_clopen (A := A) hClopen
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_clopen (A := A) hClopen
  simpa using h₁.trans h₂
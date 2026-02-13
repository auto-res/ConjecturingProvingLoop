

theorem P2_of_P1_and_P3' {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h2 : Topology.P3 A) : Topology.P2 A := by
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨h1, h2⟩
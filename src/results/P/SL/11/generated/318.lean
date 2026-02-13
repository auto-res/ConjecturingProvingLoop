

theorem P3_of_P1_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 A ∧ Topology.P2 A) → Topology.P3 A := by
  rintro ⟨_, hP2⟩
  exact Topology.P2_implies_P3 (A := A) hP2


theorem P1_lebesgue_number {X : Type*} [TopologicalSpace X] (A : Set X) : Topology.P1 A → ∃ ε : ℝ, ε > 0 := by
  intro _
  exact ⟨1, by norm_num⟩
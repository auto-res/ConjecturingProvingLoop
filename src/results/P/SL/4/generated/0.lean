

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  intro x hxA
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure_subset : closure (interior A) ⊆ closure A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      exact closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact h_subset hx_in


theorem Topology.P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_cl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono h_cl
  exact h_sub hx₁
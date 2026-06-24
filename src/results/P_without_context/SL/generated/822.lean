

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P3]
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_sub : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact (interior_subset : interior A ⊆ A)
    exact this
  exact h_sub hx₁
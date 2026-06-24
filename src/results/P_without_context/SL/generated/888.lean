

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P3 A := by
  intro hP2
  dsimp [P2] at hP2
  dsimp [P3]
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h_closure : closure (interior A) ⊆ closure A := by
      have h_int : interior A ⊆ A := interior_subset
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx₁
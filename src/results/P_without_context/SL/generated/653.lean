

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 A → P1 A ∧ P3 A := by
  intro h
  have hP1 : P1 A := by
    dsimp [P1]
    intro x hxA
    have : x ∈ interior (closure (interior A)) := h hxA
    exact interior_subset this
  have hP3 : P3 A := by
    dsimp [P3]
    intro x hxA
    have hx : x ∈ interior (closure (interior A)) := h hxA
    have h_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
      apply interior_mono
      apply closure_mono
      exact interior_subset
    exact h_subset hx
  exact And.intro hP1 hP3
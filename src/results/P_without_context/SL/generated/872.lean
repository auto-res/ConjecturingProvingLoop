

theorem P2_implies_P3 {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2] at h
  dsimp [P3]
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h₀ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono h₀
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := h hxA
  exact h₁ hx
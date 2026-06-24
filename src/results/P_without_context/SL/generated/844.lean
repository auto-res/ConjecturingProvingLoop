

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro h₂
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := h₂ hx
  have hx₂ : x ∈ closure (interior A) :=
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx₁
  exact hx₂
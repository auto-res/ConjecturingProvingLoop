

theorem P1_of_P2 {A : Set X} : P2 A → P1 A := by
  intro hP2
  unfold P1 P2 at *
  exact hP2.trans interior_subset

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  unfold P1 at *
  intro x hx
  cases hx with
  | inl hAx =>
      have hx₁ : x ∈ closure (interior A) := hA hAx
      have hSub : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_left)
      exact hSub hx₁
  | inr hBx =>
      have hx₁ : x ∈ closure (interior B) := hB hBx
      have hSub : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono Set.subset_union_right)
      exact hSub hx₁

theorem P3_closed_of_open {A : Set X} (h₁ : IsClosed A) (h₂ : IsOpen A) : P3 A := by
  intro x hx
  simpa [h₁.closure_eq, h₂.interior_eq] using hx
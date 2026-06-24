

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hxA =>
      -- x ∈ A
      have hx' : x ∈ closure (interior A) := hA hxA
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_subset hx'
  | inr hxB =>
      -- x ∈ B
      have hx' : x ∈ closure (interior B) := hB hxB
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_subset hx'

theorem P2_empty : P2 (∅ : Set X) := by
  dsimp [P2]
  intro x hx
  cases hx

theorem P2_implies_P1 {A : Set X} (h : P2 A) : P1 A := by
  dsimp [P1, P2]
  intro x hx
  exact interior_subset (h hx)

theorem P1_closure_eq_closure_interior {A : Set X} (h : P1 A) : closure (interior A) = closure A := by
  apply Set.Subset.antisymm
  · exact closure_mono interior_subset
  · exact closure_minimal h isClosed_closure
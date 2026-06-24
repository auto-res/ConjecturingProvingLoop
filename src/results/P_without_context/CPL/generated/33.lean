

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  simpa [P1, interior_univ, closure_univ]

theorem exists_P2_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B : Set X, B ⊆ A ∧ P2 B := by
  refine ⟨(∅ : Set X), ?_, ?_⟩
  · simp
  · simpa [P2]

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hA hxA
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact this
      exact h_sub hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hB hxB
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        have : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact this
      exact h_sub hx'
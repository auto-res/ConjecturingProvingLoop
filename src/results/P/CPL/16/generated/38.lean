

theorem exists_P1_proper_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : A.Nonempty) : ∃ B, B ⊂ A ∧ P1 B := by
  refine ⟨(∅ : Set X), ?_, P1_empty⟩
  have hsub : (∅ : Set X) ⊆ A := Set.empty_subset _
  have hnot : ¬ A ⊆ (∅ : Set X) := by
    intro h
    rcases hA with ⟨x, hx⟩
    have : x ∈ (∅ : Set X) := h hx
    exact this
  exact ⟨hsub, hnot⟩
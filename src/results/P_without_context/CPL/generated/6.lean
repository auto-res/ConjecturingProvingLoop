

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P3 A := by
  dsimp [P2, P3] at *
  intro x hx
  have hx1 := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    have : closure (interior A) ⊆ closure A := by
      apply closure_mono
      exact interior_subset
    exact this
  exact hsubset hx1

theorem P1_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  dsimp [P1] at *
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h i) hxi
  have h_subset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hi_subset : (A i) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hi_subset
    exact closure_mono h_int_subset
  exact h_subset hx_cl

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  dsimp [P1]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  dsimp [P2]
  intro x hx
  cases hx
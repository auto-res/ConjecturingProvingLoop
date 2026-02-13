

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ interior (closure A) := hA hxA
      -- We show the required inclusion.
      have h_subset :
          (interior (closure A) : Set X) ⊆ interior (closure (A ∪ B)) := by
        -- First, `closure A ⊆ closure (A ∪ B)`.
        have h_closure : (closure A : Set X) ⊆ closure (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact closure_mono h_sub
        -- Pass to interiors.
        exact interior_mono h_closure
      exact h_subset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ interior (closure B) := hB hxB
      -- Show the required inclusion for `B`.
      have h_subset :
          (interior (closure B) : Set X) ⊆ interior (closure (A ∪ B)) := by
        -- `closure B ⊆ closure (A ∪ B)`.
        have h_closure : (closure B : Set X) ⊆ closure (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact closure_mono h_sub
        -- Pass to interiors.
        exact interior_mono h_closure
      exact h_subset hxB'

theorem P3_Unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P3 (A i)) : P3 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_i' : x ∈ interior (closure (A i)) := (h i) hx_i
  have h_subset :
      (interior (closure (A i)) : Set X) ⊆
        interior (closure (⋃ j, A j)) := by
    have h_closure :
        (closure (A i) : Set X) ⊆ closure (⋃ j, A j) := by
      have h_sub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_sub
    exact interior_mono h_closure
  exact h_subset hx_i'

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P1 A) : P1 (interior A) := by
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this
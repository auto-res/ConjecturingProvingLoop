

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P2_unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P2 (A i)) : P2 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_i' : x ∈ interior (closure (interior (A i))) := (h i) hx_i
  have h_subset :
      (interior (closure (interior (A i))) : Set X) ⊆
        interior (closure (interior (⋃ j, A j))) := by
    -- First, establish `interior (A i) ⊆ interior (⋃ j, A j)`.
    have h₁ : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have hA_i_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hA_i_subset
    -- Then, take closures and apply monotonicity again.
    have h₂ : (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, A j)) := closure_mono h₁
    -- Finally, pass to interiors.
    exact interior_mono h₂
  exact h_subset hx_i'
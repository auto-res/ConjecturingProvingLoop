

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P2 (interior A) := by
  intro x hx
  -- First, see `x` as an element of `A` to make use of `h : P2 A`.
  have hxA : x ∈ (A : Set X) :=
    (interior_subset : (interior A : Set X) ⊆ A) hx
  -- Apply `h` to obtain membership in the desired interior.
  have h'x : x ∈ interior (closure (interior A)) := h hxA
  -- Rewrite the goal using `interior_interior`.
  simpa [interior_interior] using h'x

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ interior (closure (interior A)) := hA hxA
      -- We show the required monotone inclusion.
      have h_subset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- First, `interior A ⊆ interior (A ∪ B)`.
        have h₁ : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have hA_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hA_sub
        -- Then, `closure (interior A) ⊆ closure (interior (A ∪ B))`.
        have h₂ : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        -- Finally, apply `interior_mono`.
        exact interior_mono h₂
      exact h_subset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ interior (closure (interior B)) := hB hxB
      -- Again prove the required inclusion.
      have h_subset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) := by
        -- `interior B ⊆ interior (A ∪ B)`.
        have h₁ : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have hB_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hB_sub
        -- `closure (interior B) ⊆ closure (interior (A ∪ B))`.
        have h₂ : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        -- Apply `interior_mono`.
        exact interior_mono h₂
      exact h_subset hxB'

theorem P1_Unionᵢ {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} (h : ∀ i, P1 (A i)) : P1 (⋃ i, A i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (A i)) := (h i) hx_i
  have h_subset :
      (closure (interior (A i)) : Set X) ⊆
        closure (interior (⋃ j, A j)) := by
    have h_int_subset :
        (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have hA_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono hA_subset
    exact closure_mono h_int_subset
  exact h_subset hx_cl
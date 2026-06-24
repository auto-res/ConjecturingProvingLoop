

theorem P3_of_P2 {A : Set X} (hA : P2 (A)) : P3 (A) := by
  dsimp [P2] at hA
  dsimp [P3]
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := hA hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact interior_mono hcl
  exact hsubset hx₁

theorem P1_Union {ι : Sort _} (s : ι → Set X) (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  dsimp [P1] at h ⊢
  intro x hx
  rcases (Set.mem_iUnion).1 hx with ⟨i, hx_i⟩
  have hx_cl : x ∈ closure (interior (s i)) := h i hx_i
  have h_subset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    have h_int : interior (s i) ⊆ interior (⋃ j, s j) := by
      have h_set : (s i) ⊆ ⋃ j, s j := by
        intro y hy
        exact (Set.mem_iUnion).2 ⟨i, hy⟩
      exact interior_mono h_set
    exact closure_mono h_int
  exact h_subset hx_cl

theorem P1_interior {A : Set X} : P1 (interior (A)) := by
  dsimp [P1]
  intro x hx
  have hx_cl : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using hx_cl

theorem P2_interior_closure {A : Set X} : P2 (interior (closure (A))) := by
  dsimp [P2]
  intro x hx
  -- Step 1: obtain a convenient inclusion
  have h_subset :
      interior (closure A) ⊆ interior (closure (interior (closure A))) := by
    -- A set is contained in the closure of itself
    have h₁ : interior (closure A) ⊆ closure (interior (closure A)) :=
      subset_closure
    -- Taking interiors on both sides
    have h₂ :
        interior (interior (closure A)) ⊆
          interior (closure (interior (closure A))) :=
      interior_mono h₁
    -- Eliminate the double `interior`
    simpa [interior_interior] using h₂
  -- Step 2: apply the inclusion to `x` and conclude
  have : x ∈ interior (closure (interior (closure A))) := h_subset hx
  simpa [interior_interior] using this


theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hx_i⟩
  -- `x` is in `s i`, hence in `closure (interior (s i))`
  have hx_closure : x ∈ closure (interior (s i)) := (h i) hx_i
  -- show that this closure is contained in the desired one
  have h_subset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    -- `interior (s i)` is contained in `interior (⋃ j, s j)`
    have h_int : (interior (s i) : Set X) ⊆ interior (⋃ j, s j) := by
      have h_s : (s i : Set X) ⊆ ⋃ j, s j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_s
    exact closure_mono h_int
  exact h_subset hx_closure
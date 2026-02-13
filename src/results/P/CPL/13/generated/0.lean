

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  dsimp [P2, P1] at *
  exact Set.Subset.trans hP2 interior_subset

theorem P2_of_open {A : Set X} (h : IsOpen A) : P2 A := by
  -- Unfold the definition of `P2`
  dsimp [P2]
  intro x hxA
  -- Since `A` is open, its interior is itself
  have hx_int : x ∈ interior A := by
    simpa [h.interior_eq] using hxA
  -- Show `interior A ⊆ interior (closure (interior A))`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    -- `interior A` is contained in its closure
    have h_closure : interior A ⊆ closure (interior A) := by
      intro y hy
      exact subset_closure hy
    -- Use maximality of the interior
    exact interior_maximal h_closure isOpen_interior
  -- Conclude
  exact h_subset hx_int

theorem P1_union {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  -- Unfold the definition of `P1`
  dsimp [P1] at *
  intro x hx
  cases hx with
  | inl hA_mem =>
      -- `x` comes from `A`
      have hxA : x ∈ closure (interior A) := hA hA_mem
      -- `interior A` is contained in `interior (A ∪ B)`
      have h_subset : interior A ⊆ interior (A ∪ B) := interior_mono (by
        intro y hy
        exact Or.inl hy)
      -- Hence, `x` is in the desired closure
      exact (closure_mono h_subset) hxA
  | inr hB_mem =>
      -- `x` comes from `B`
      have hxB : x ∈ closure (interior B) := hB hB_mem
      -- `interior B` is contained in `interior (A ∪ B)`
      have h_subset : interior B ⊆ interior (A ∪ B) := interior_mono (by
        intro y hy
        exact Or.inr hy)
      -- Hence, `x` is in the desired closure
      exact (closure_mono h_subset) hxB

theorem closure_eq_of_P1 {A : Set X} (hA : P1 A) : closure (interior A) = closure A := by
  apply Set.Subset.antisymm
  ·
    exact closure_mono interior_subset
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using h
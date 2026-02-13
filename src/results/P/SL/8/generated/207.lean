

theorem interior_diff_closed_eq {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  classical
  -- Prove the mutual inclusions.
  apply Set.Subset.antisymm
  · -- `interior (A \ B) ⊆ interior A \ B`
    intro x hx
    -- We already have the more precise inclusion into `interior A \ closure B`.
    have hsubset : interior (A \ B) ⊆ interior A \ closure B :=
      interior_diff_subset (X := X) (A := A) (B := B)
    have hx' := hsubset hx
    -- Since `B` is closed, `closure B = B`.
    simpa [hB_closed.closure_eq] using hx'
  · -- `interior A \ B ⊆ interior (A \ B)`
    rintro x ⟨hxIntA, hxNotB⟩
    -- Choose an open neighbourhood `U` of `x` contained in `A`.
    rcases (Set.mem_interior).1 hxIntA with ⟨U, hU_open, hU_subA, hxU⟩
    -- Consider the open set `V = U \ B`.
    have hV_open : IsOpen (U \ B) := by
      -- The complement of `B` is open because `B` is closed.
      have hOpenCompl : IsOpen (Bᶜ) := by
        simpa using (isOpen_compl_iff).2 hB_closed
      -- `U \ B = U ∩ Bᶜ`.
      simpa [Set.diff_eq] using hU_open.inter hOpenCompl
    -- `V` is contained in `A \ B`.
    have hV_sub : U \ B ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyU, hyNotB⟩
      exact And.intro (hU_subA hyU) hyNotB
    -- `x` lies in `V`.
    have hxV : x ∈ U \ B := by
      exact And.intro hxU hxNotB
    -- Conclude that `x` is in the interior of `A \ B`.
    exact
      (Set.mem_interior).2 ⟨U \ B, hV_open, hV_sub, hxV⟩
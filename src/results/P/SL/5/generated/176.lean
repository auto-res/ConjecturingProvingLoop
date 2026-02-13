

theorem interior_inter_of_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) :
    interior (A ∩ B : Set X) = A ∩ interior B := by
  -- We establish both inclusions and then apply `le_antisymm`.
  apply le_antisymm
  · -- `interior (A ∩ B) ⊆ A ∩ interior B`
    intro x hx
    have hxA : x ∈ A := by
      -- `interior (A ∩ B) ⊆ interior A = A` because `A` is open.
      have : x ∈ interior A :=
        (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
      simpa [hA.interior_eq] using this
    have hxIntB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact ⟨hxA, hxIntB⟩
  · -- `A ∩ interior B ⊆ interior (A ∩ B)`
    intro x hx
    rcases hx with ⟨hxA, hxIntB⟩
    -- The set `U = A ∩ interior B` is an open neighborhood of `x`
    -- contained in `A ∩ B`.
    have hUopen : IsOpen (A ∩ interior B : Set X) :=
      hA.inter isOpen_interior
    have hUsub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨hy.1, interior_subset hy.2⟩
    have hxU : x ∈ (A ∩ interior B : Set X) := ⟨hxA, hxIntB⟩
    exact (mem_interior.2 ⟨A ∩ interior B, hUsub, hUopen, hxU⟩)
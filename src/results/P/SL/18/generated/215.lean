

theorem interior_inter {α : Type*} [TopologicalSpace α] {A B : Set α} :
    interior (A ∩ B) = interior A ∩ interior B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set α) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set α) ⊆ B)) hx
    exact And.intro hxA hxB
  · intro x hx
    rcases hx with ⟨hxA, hxB⟩
    -- The set `interior A ∩ interior B` is open and contained in `A ∩ B`.
    have hOpen : IsOpen (interior A ∩ interior B) :=
      (isOpen_interior).inter isOpen_interior
    have hSub : (interior A ∩ interior B : Set α) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1,
             (interior_subset : interior B ⊆ B) hy.2⟩
    have hIncl : (interior A ∩ interior B : Set α) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    exact hIncl ⟨hxA, hxB⟩
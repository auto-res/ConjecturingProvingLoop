

theorem interior_diff_eq_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    -- `x` belongs to `interior A` because `A \ B ⊆ A`.
    have hxIntA : x ∈ interior A :=
      (interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)) hx
    -- `x` is not in `B` since it lies in `A \ B`.
    have hxNotB : x ∉ B := by
      have : x ∈ (A \ B : Set X) :=
        (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx
      exact this.2
    exact ⟨hxIntA, hxNotB⟩
  · rintro ⟨hxIntA, hxNotB⟩
    -- The set `interior A \ B` is an open neighbourhood of `x`
    -- contained in `A \ B`, so `x` lies in the interior of `A \ B`.
    have hOpen : IsOpen ((interior A) \ B : Set X) :=
      IsOpen.diff isOpen_interior hB_closed
    have hxIn : x ∈ (interior A) \ B := ⟨hxIntA, hxNotB⟩
    -- `interior A \ B` is contained in `A \ B`.
    have hSub : ((interior A) \ B : Set X) ⊆ A \ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    exact (interior_maximal hSub hOpen) hxIn
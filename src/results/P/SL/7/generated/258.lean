

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen (B : Set X)) :
    interior (A ∩ B : Set X) = interior A ∩ B := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (A ∩ B)` we get `x ∈ interior A`.
    have hxIntA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    -- And `x ∈ B` because the interior is contained in the set itself.
    have hxB : x ∈ B := ((interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx).2
    exact ⟨hxIntA, hxB⟩
  · intro hx
    rcases hx with ⟨hxIntA, hxB⟩
    -- The open set we will use in the maximality argument.
    have hOpen : IsOpen (interior A ∩ B) :=
      isOpen_interior.inter hB
    -- This open set is contained in `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨(interior_subset : interior A ⊆ A) hy.1, hy.2⟩
    -- Hence it is contained in the interior of `A ∩ B`.
    have hIncl : (interior A ∩ B : Set X) ⊆ interior (A ∩ B) :=
      interior_maximal hSub hOpen
    -- Since `x ∈ interior A ∩ B`, we obtain `x ∈ interior (A ∩ B)`.
    exact hIncl ⟨hxIntA, hxB⟩
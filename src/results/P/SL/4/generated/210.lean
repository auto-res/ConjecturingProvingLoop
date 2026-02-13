

theorem interior_inter_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    interior (A ∩ B) = interior A ∩ B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A ∩ B := interior_subset hx
    have hxB : x ∈ B := hAB.2
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    have hxIntA : x ∈ interior A := (interior_mono hSub) hx
    exact And.intro hxIntA hxB
  · rintro ⟨hxIntA, hxB⟩
    -- Consider the open set `interior A ∩ B` containing `x`.
    have hOpen : IsOpen (interior A ∩ B) := isOpen_interior.inter hB
    have hxMem : x ∈ interior A ∩ B := And.intro hxIntA hxB
    -- This open set is contained in `A ∩ B`.
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy; exact And.intro (interior_subset hy.1) hy.2
    -- Hence `A ∩ B` belongs to the neighbourhoods of `x`.
    have hNhd : (A ∩ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hxMem) hSub
    -- Conclude that `x` is in the interior of `A ∩ B`.
    exact (mem_interior_iff_mem_nhds).2 hNhd


theorem interior_inter_of_isOpen_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A ∩ B) = A ∩ interior B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A ∩ B := interior_subset hx
    have hxA : x ∈ A := hAB.1
    have hxIntB : x ∈ interior B := by
      have hSub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono hSub) hx
    exact And.intro hxA hxIntB
  · rintro ⟨hxA, hxIntB⟩
    -- Consider the open set `A ∩ interior B` containing `x`.
    have hOpen : IsOpen (A ∩ interior B) := hA.inter isOpen_interior
    have hMem₁ : x ∈ (A ∩ interior B) := And.intro hxA hxIntB
    -- This open set is contained in `A ∩ B`.
    have hSub : (A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact And.intro hy.1 (interior_subset hy.2)
    -- Hence `A ∩ B` belongs to the neighbourhoods of `x`.
    have hMem₂ : (A ∩ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hMem₁) hSub
    -- Conclude that `x` is in the interior of `A ∩ B`.
    exact (mem_interior_iff_mem_nhds).2 hMem₂
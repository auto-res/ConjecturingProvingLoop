

theorem interior_diff_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  ext x
  constructor
  · intro hx
    have hAB : x ∈ A \ B := interior_subset hx
    -- `A \ B ⊆ A`, hence `x ∈ interior A`
    have hIntA : x ∈ interior A := by
      have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
      exact (interior_mono hSub) hx
    exact And.intro hIntA hAB.2
  · rintro ⟨hxIntA, hxNotB⟩
    -- Build an open neighborhood contained in `A \ B`
    have hOpen : IsOpen (interior A ∩ Bᶜ) :=
      isOpen_interior.inter hB.isOpen_compl
    have hMem  : x ∈ interior A ∩ Bᶜ := And.intro hxIntA hxNotB
    have hSub  : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
      intro y hy
      exact And.intro (interior_subset hy.1) hy.2
    -- Conclude that `x` belongs to `interior (A \ B)`
    have : (A \ B : Set X) ∈ nhds x :=
      Filter.mem_of_superset (hOpen.mem_nhds hMem) hSub
    exact (mem_interior_iff_mem_nhds).2 this


theorem Topology.interior_inter_three_eq {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    interior (A ∩ B ∩ C : Set X) =
      interior A ∩ interior B ∩ interior C := by
  -- We prove the two inclusions separately and finish with antisymmetry.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    intro x hx
    -- `x ∈ interior A`
    have hxA : x ∈ interior A := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ A := by
        intro y hy; exact hy.1.1
      exact (interior_mono h_sub) hx
    -- `x ∈ interior B`
    have hxB : x ∈ interior B := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ B := by
        intro y hy; exact hy.1.2
      exact (interior_mono h_sub) hx
    -- `x ∈ interior C`
    have hxC : x ∈ interior C := by
      have h_sub : (A ∩ B ∩ C : Set X) ⊆ C := by
        intro y hy; exact hy.2
      exact (interior_mono h_sub) hx
    exact And.intro (And.intro hxA hxB) hxC
  · -- `⊇` direction
    intro x hx
    rcases hx with ⟨⟨hxA, hxB⟩, hxC⟩
    -- The open set `interior A ∩ interior B ∩ interior C`
    -- will witness that `x` is in the interior of `A ∩ B ∩ C`.
    have h_open :
        IsOpen (interior A ∩ interior B ∩ interior C : Set X) := by
      have hAB :
          IsOpen (interior A ∩ interior B : Set X) :=
        (isOpen_interior : IsOpen (interior A)).inter
          (isOpen_interior : IsOpen (interior B))
      exact hAB.inter (isOpen_interior : IsOpen (interior C))
    -- This open set is contained in `A ∩ B ∩ C`.
    have h_subset :
        (interior A ∩ interior B ∩ interior C : Set X) ⊆
          A ∩ B ∩ C := by
      intro y hy
      have hyA : y ∈ A := interior_subset hy.1.1
      have hyB : y ∈ B := interior_subset hy.1.2
      have hyC : y ∈ C := interior_subset hy.2
      exact And.intro (And.intro hyA hyB) hyC
    -- `x` belongs to the open set.
    have hx_open :
        x ∈ (interior A ∩ interior B ∩ interior C : Set X) :=
      And.intro (And.intro hxA hxB) hxC
    -- Hence `x` belongs to the interior of `A ∩ B ∩ C`.
    have h_mem :
        x ∈ interior (A ∩ B ∩ C : Set X) :=
      (interior_maximal h_subset h_open) hx_open
    exact h_mem
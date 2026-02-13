

theorem interior_inter_of_isOpen_right
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ B := by
  apply Set.Subset.antisymm
  · intro x hx
    have hA : x ∈ interior A := by
      -- `A ∩ B ⊆ A`
      have hSub : (A ∩ B : Set X) ⊆ A := by
        intro y hy
        exact hy.1
      exact (interior_mono hSub) hx
    have hBmem : x ∈ B := by
      have : x ∈ (A ∩ B : Set X) :=
        (interior_subset : interior (A ∩ B) ⊆ A ∩ B) hx
      exact this.2
    exact And.intro hA hBmem
  · intro x hx
    rcases hx with ⟨hIntA, hBx⟩
    -- `x` lies in `interior A ∩ B`
    have hxInter : x ∈ interior A ∩ B := And.intro hIntA hBx
    -- `interior A ∩ B` is open
    have hOpen : IsOpen (interior A ∩ B) :=
      (isOpen_interior).inter hB
    -- Inclusion `interior A ∩ B ⊆ A ∩ B`
    have hSub : (interior A ∩ B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact
        And.intro
          ((interior_subset : interior A ⊆ A) hy.1)
          hy.2
    -- Place `x` inside `interior (A ∩ B)`
    have : x ∈ interior (A ∩ B) :=
      (interior_maximal hSub hOpen) hxInter
    exact this


theorem interior_diff_subset_diff_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ A \ closure B := by
  intro x hxInt
  -- From the interior membership we deduce `x ∈ A \ B`.
  have hMem : x ∈ A \ B :=
    (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hxInt
  have hxA : x ∈ A := hMem.1
  -- We now show that `x ∉ closure B`.
  have hxNotCl : x ∉ closure B := by
    intro hxCl
    -- `interior (A \ B)` is an open neighbourhood of `x` disjoint from `B`,
    -- contradicting the definition of `closure`.
    have hNonempty :
        ((interior (A \ B : Set X)) ∩ B : Set X).Nonempty :=
      (mem_closure_iff).1 hxCl (interior (A \ B : Set X))
        isOpen_interior hxInt
    rcases hNonempty with ⟨y, ⟨hyInt, hyB⟩⟩
    have : y ∈ A \ B :=
      (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hyInt
    exact this.2 hyB
  exact ⟨hxA, hxNotCl⟩
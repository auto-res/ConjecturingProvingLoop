

theorem Topology.frontier_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier (A ∩ B) ⊆ frontier A ∪ frontier B := by
  intro x hx
  rcases hx with ⟨hxClosInter, hxNotIntInter⟩
  -- `x` belongs to both closures
  have hxClosA : x ∈ closure A := by
    have hSub : (A ∩ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hxClosInter
  have hxClosB : x ∈ closure B := by
    have hSub : (A ∩ B : Set X) ⊆ B := fun y hy => hy.2
    exact (closure_mono hSub) hxClosInter
  open Classical in
  by_cases hIntA : x ∈ interior A
  · -- `x ∈ interior A`
    by_cases hIntB : x ∈ interior B
    · -- `x ∈ interior B` as well: contradiction with `hxNotIntInter`
      have hIntInter : x ∈ interior (A ∩ B) := by
        -- `interior A ∩ interior B` is an open set contained in `A ∩ B`
        have hSub : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
          intro y hy; exact ⟨interior_subset hy.1, interior_subset hy.2⟩
        have hOpen : IsOpen (interior A ∩ interior B) :=
          isOpen_interior.inter isOpen_interior
        have hInc := interior_maximal hSub hOpen
        exact hInc ⟨hIntA, hIntB⟩
      exact False.elim (hxNotIntInter hIntInter)
    · -- `x ∉ interior B` ⇒ `x ∈ frontier B`
      exact Or.inr ⟨hxClosB, hIntB⟩
  · -- `x ∉ interior A` ⇒ `x ∈ frontier A`
    exact Or.inl ⟨hxClosA, hIntA⟩
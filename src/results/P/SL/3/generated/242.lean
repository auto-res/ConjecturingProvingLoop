

theorem boundary_inter_subset_boundary {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure ((A ∩ B) : Set X) \ interior ((A ∩ B) : Set X) ⊆
      (closure (A : Set X) \ interior (A : Set X)) ∪
        (closure (B : Set X) \ interior (B : Set X)) := by
  classical
  intro x hx
  rcases hx with ⟨hClAB, hNotIntAB⟩
  -- `x` is in the closures of both `A` and `B`
  have hClA : (x : X) ∈ closure (A : Set X) := by
    have hSub : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
      apply closure_mono; exact Set.inter_subset_left
    exact hSub hClAB
  have hClB : (x : X) ∈ closure (B : Set X) := by
    have hSub : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
      apply closure_mono; exact Set.inter_subset_right
    exact hSub hClAB
  -- Case distinction on membership in the interiors of `A` and `B`
  by_cases hIntA : (x : X) ∈ interior (A : Set X)
  · by_cases hIntB : (x : X) ∈ interior (B : Set X)
    · -- If `x` is in both interiors, then it lies in the interior of `A ∩ B`,
      -- contradicting `hNotIntAB`.
      have hOpen : IsOpen (interior (A : Set X) ∩ interior (B : Set X)) :=
        isOpen_interior.inter isOpen_interior
      have hxIn : (x : X) ∈ interior (A : Set X) ∩ interior (B : Set X) :=
        And.intro hIntA hIntB
      have hxIntOpen : (x : X) ∈ interior (interior (A : Set X) ∩ interior (B : Set X)) := by
        simpa [hOpen.interior_eq] using hxIn
      have hSubset :
          interior (A : Set X) ∩ interior (B : Set X) ⊆ (A ∩ B : Set X) := by
        intro y hy; exact And.intro (interior_subset hy.1) (interior_subset hy.2)
      have : (x : X) ∈ interior ((A ∩ B) : Set X) :=
        (interior_mono hSubset) hxIntOpen
      exact (hNotIntAB this).elim
    · -- `x ∉ interior B` ⇒ `x` is on the boundary of `B`
      exact Or.inr ⟨hClB, hIntB⟩
  · -- `x ∉ interior A` ⇒ `x` is on the boundary of `A`
    exact Or.inl ⟨hClA, hIntA⟩
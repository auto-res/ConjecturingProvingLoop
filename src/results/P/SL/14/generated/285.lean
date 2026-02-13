

theorem Topology.interiorClosure_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure A) ∪ interior (closure B) ∪ interior (closure C) ⊆
      interior (closure (A ∪ B ∪ C)) := by
  intro x hx
  -- Break the membership in the three‐fold union into cases.
  rcases hx with hxAB | hxC
  · -- `x ∈ interior (closure A) ∪ interior (closure B)`
    rcases hxAB with hxA | hxB
    · -- Subcase: `x ∈ interior (closure A)`
      -- First enlarge to `A ∪ B`.
      have hxAB : (x : X) ∈ interior (closure (A ∪ B)) := by
        have h :=
          Topology.interiorClosure_subset_interiorClosure_union_left
            (X := X) (A := A) (B := B)
        exact h hxA
      -- Then enlarge to `A ∪ B ∪ C`.
      have hABsubset :
          interior (closure (A ∪ B)) ⊆ interior (closure (A ∪ B ∪ C)) := by
        have hSubset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inl hy
        exact
          Topology.interiorClosure_mono
            (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) hSubset
      exact hABsubset hxAB
    · -- Subcase: `x ∈ interior (closure B)`
      have hxAB : (x : X) ∈ interior (closure (A ∪ B)) := by
        have h :=
          Topology.interiorClosure_subset_interiorClosure_union_right
            (X := X) (A := A) (B := B)
        exact h hxB
      have hABsubset :
          interior (closure (A ∪ B)) ⊆ interior (closure (A ∪ B ∪ C)) := by
        have hSubset : (A ∪ B : Set X) ⊆ A ∪ B ∪ C := by
          intro y hy
          exact Or.inl hy
        exact
          Topology.interiorClosure_mono
            (X := X) (A := A ∪ B) (B := A ∪ B ∪ C) hSubset
      exact hABsubset hxAB
  · -- Case: `x ∈ interior (closure C)`
    have hCsubset :
        interior (closure C) ⊆ interior (closure (A ∪ B ∪ C)) := by
      have hSubset : (C : Set X) ⊆ A ∪ B ∪ C := by
        intro y hy
        exact Or.inr hy
      exact
        Topology.interiorClosure_mono
          (X := X) (A := C) (B := A ∪ B ∪ C) hSubset
    exact hCsubset hxC
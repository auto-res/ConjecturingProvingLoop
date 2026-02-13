

theorem Topology.P3_union_left_dense {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure A = (Set.univ : Set X)) :
    Topology.P3 (X := X) (A ∪ B) := by
  -- First show that `A ∪ B` is dense in `X`.
  have h_dense_union : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro x _
      simp
    · intro x _
      -- Since `closure A = univ`, we have `x ∈ closure A`.
      have hxA : x ∈ closure A := by
        simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
      -- And `closure A ⊆ closure (A ∪ B)` because `A ⊆ A ∪ B`.
      have h_sub : closure A ⊆ closure (A ∪ B) := closure_mono (by
        intro y hy
        exact Or.inl hy)
      exact h_sub hxA
  -- Conclude using `P3_of_dense`.
  exact Topology.P3_of_dense (X := X) (A := A ∪ B) h_dense_union
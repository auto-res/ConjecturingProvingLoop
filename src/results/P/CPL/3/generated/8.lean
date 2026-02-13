

theorem P3_of_exists_dense_subset {X : Type*} [TopologicalSpace X] {A : Set X} : (∃ B, B ⊆ A ∧ closure B = Set.univ) → P3 A := by
  rintro ⟨B, hB_sub, hB_dense⟩
  intro x hxA
  -- First, deduce that `closure A = univ`.
  have hA_dense : closure A = (Set.univ : Set X) := by
    apply subset_antisymm
    · intro y hy
      trivial
    ·
      have hsubset : closure B ⊆ closure A := closure_mono hB_sub
      simpa [hB_dense] using hsubset
  -- With this, the conclusion follows immediately.
  simpa [hA_dense, interior_univ] using (Set.mem_univ x)
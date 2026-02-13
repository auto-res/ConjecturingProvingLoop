

theorem P3_of_dense_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = Set.univ → P3 A := by
  intro hDense
  -- First show that `closure A = univ`
  have hClosureA : (closure (A : Set X) : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    ·
      have hsubset : (closure (interior A) : Set X) ⊆ closure A :=
        closure_mono (interior_subset : interior A ⊆ A)
      simpa [hDense] using hsubset
  -- Conclude `P3 A`
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hClosureA, interior_univ] using this
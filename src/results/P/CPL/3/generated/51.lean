

theorem P1_Union_dense {X : Type*} [TopologicalSpace X] {ι : Sort*} {s : ι → Set X} (h : ∀ i, closure (interior (s i)) = Set.univ) : P1 (⋃ i, s i) := by
  -- First, turn the density assumption into `P1` for each individual set.
  have hP1 : ∀ i, P1 (s i) :=
    fun i => P1_of_dense_interior (X := X) (A := s i) (h i)
  -- Then apply the `P1`-closure under arbitrary unions.
  exact P1_iUnion hP1
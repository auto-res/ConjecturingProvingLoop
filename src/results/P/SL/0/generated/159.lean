

theorem interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    interior (closure (A : Set X)) = (Set.univ : Set X) := by
  -- First, translate the density assumption into an interior statement.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using
      (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))
  -- Monotonicity of `closure` and `interior` yields the key inclusion.
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hCl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hCl
  -- Hence `univ ⊆ interior (closure A)`.
  have hUnivSub :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hIntUniv] using hMono
  -- The reverse inclusion is trivial.
  have hSubUniv :
      interior (closure (A : Set X)) ⊆ (Set.univ : Set X) :=
    Set.subset_univ _
  exact Set.Subset.antisymm hSubUniv hUnivSub
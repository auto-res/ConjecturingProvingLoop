

theorem dense_interior_satisfies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, deduce that `closure A = univ`.
  have hClosure_eq : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A) ⊆ closure A`
    have hSub : closure (interior (A : Set X)) ⊆ closure A :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Rewrite the left-hand side using `hDense`.
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [hDense] using hSub
    -- Combine the inclusions to obtain equality.
    exact Set.Subset.antisymm (Set.subset_univ _) this
  -- Therefore, the interior of `closure A` is the entire space.
  have hInt_eq : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [hClosure_eq] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Conclude the required membership.
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInt_eq] using this


theorem Topology.dense_interior_implies_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) → closure (A : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- `closure (interior A)` is the whole space because `interior A` is dense.
  have hInt : closure (interior (A : Set X)) = (Set.univ : Set X) := hDense.closure_eq
  -- Monotonicity of `closure` for the inclusion `interior A ⊆ A`.
  have hUnivSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    have hMono : (closure (interior (A : Set X)) : Set X) ⊆ closure (A : Set X) := by
      have hSub : (interior (A : Set X) : Set X) ⊆ A := interior_subset
      exact closure_mono hSub
    simpa [hInt] using hMono
  -- Combine with the trivial inclusion `closure A ⊆ univ`.
  apply Set.Subset.antisymm
  · intro x hx; simp
  · exact hUnivSub


theorem Topology.dense_of_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) → Dense (A : Set X) := by
  intro hClosureInt
  -- First, show that `closure A = univ`.
  have hSubset : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    -- Since `interior A ⊆ A`, taking closures yields
    -- `closure (interior A) ⊆ closure A`.
    have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hClosureInt] using hIncl
  have hSuperset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _hx
    simp
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSuperset hSubset
  exact (dense_iff_closure_eq).2 hClosureA
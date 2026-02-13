

theorem Topology.denseInterior_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (X := X) A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  -- First, show that `closure A = univ`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    -- Since `interior A ⊆ A`, taking closures yields the inclusion we need.
    have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    -- Rewrite using the density of `interior A`.
    simpa [hDense.closure_eq] using h_subset
  have h_closureA_univ : closure (A : Set X) = (Set.univ : Set X) :=
    Set.Subset.antisymm Set.Subset_univ h_univ_subset
  -- Hence the interior of `closure A` is the whole space.
  have h_int_univ : interior (closure (A : Set X)) = (Set.univ : Set X) := by
    simpa [h_closureA_univ, interior_univ]
  -- The desired membership now follows.
  simpa [h_int_univ] using (by
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    exact this)
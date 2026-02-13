

theorem Topology.frontier_eq_compl_interior_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense (A : Set X)) :
    frontier (A : Set X) = (interior A)ᶜ := by
  classical
  -- `frontier A = closure A \ interior A`, and density gives `closure A = univ`.
  have h₁ : frontier (A : Set X) = (Set.univ : Set X) \ interior A := by
    simpa [frontier, hA.closure_eq]
  -- Rewrite `univ \ interior A` as the complement of `interior A`.
  have h₂ : (Set.univ : Set X) \ interior A = (interior A)ᶜ := by
    ext x
    by_cases hx : x ∈ interior A <;> simp [hx]
  simpa [h₁, h₂]
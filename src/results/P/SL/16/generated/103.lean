

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 (X := X) A := by
  -- First, show that `A` itself is dense, i.e. `closure A = univ`.
  have h_closure_univ : closure A = (Set.univ : Set X) := by
    -- `interior A ⊆ A`, so `closure (interior A) ⊆ closure A`.
    have h_subset : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    -- Hence every point of `univ` lies in `closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _
      -- From `h_dense`, `x ∈ closure (interior A)`.
      have hx : x ∈ closure (interior A) := by
        simpa [h_dense] using (by
          have : (x : X) ∈ (Set.univ : Set X) := by
            simp
          exact this)
      exact h_subset hx
    -- The reverse inclusion is trivial.
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _
      simp
    exact subset_antisymm h_closure_subset h_univ_subset
  -- Apply the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure_univ
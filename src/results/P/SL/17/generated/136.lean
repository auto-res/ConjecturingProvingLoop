

theorem Topology.interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- We show `closure A = Set.univ`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x _hx
      -- Since `interior (closure A) = Set.univ`, every point lies in it.
      have : x ∈ interior (closure A) := by
        simpa [hInt] using (by
          have : x ∈ (Set.univ : Set X) := by
            simp
          exact this)
      exact interior_subset this
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _hx
      simp
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  · intro hClosure
    -- From `closure A = Set.univ`, we immediately get the desired equality.
    simpa [hClosure] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
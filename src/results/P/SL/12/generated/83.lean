

theorem Topology.P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : closure (interior A : Set X) = Set.univ) :
    Topology.P3 (X := X) A := by
  -- First, show that `closure A = univ`.
  have h_closure_univ : closure (A : Set X) = (Set.univ : Set X) := by
    -- `closure (interior A)` is always contained in `closure A`.
    have h_subset : closure (interior A : Set X) ⊆ closure A :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    -- Hence `univ ⊆ closure A`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [hA] using h_subset
    -- The reverse inclusion holds trivially.
    have h_closure_subset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x hx; simp
    -- Combine the two inclusions to get the desired equality.
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  -- Conclude by applying the existing lemma for dense sets.
  exact Topology.P3_of_dense (X := X) (A := A) h_closure_univ
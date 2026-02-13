

theorem Topology.P2_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P2 (X := X) (closure A) := by
  -- First, show that `closure (interior (closure A)) = univ`.
  have h_dense : closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure (interior (closure A))`.
    have h_subset :
        closure (interior (A : Set X)) ⊆
          closure (interior (closure A)) :=
      Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A)
    -- Hence `univ ⊆ closure (interior (closure A))`.
    have h_univ_subset :
        (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
      simpa [h] using h_subset
    -- The reverse inclusion is trivial.
    have h_subset_univ :
        closure (interior (closure A)) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    -- Combine the two inclusions to obtain the equality.
    exact Set.Subset.antisymm h_subset_univ h_univ_subset
  -- Apply the existing lemma turning density of the interior into `P2`.
  exact
    Topology.P2_of_dense_interior (X := X) (A := closure A) h_dense
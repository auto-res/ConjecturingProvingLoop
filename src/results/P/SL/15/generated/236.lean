

theorem dense_of_P3_and_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      interior (closure A) = (Set.univ : Set X) →
        Dense A := by
  intro _hP3 hIntEq
  -- `interior (closure A)` is contained in `closure A`
  have h_subset : interior (closure A) ⊆ closure A := interior_subset
  -- Hence `closure A` contains all points of the space
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    simpa [hIntEq] using h_subset
  -- Combine with the trivial reverse inclusion to get equality
  have h_closure_eq : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; exact Set.mem_univ x
    · exact h_univ_subset
  -- Conclude density from the characterisation via closure
  exact (dense_iff_closure_eq (s := A)).2 h_closure_eq
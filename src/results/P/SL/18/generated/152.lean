

theorem dense_of_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior (A : Set X)) = Set.univ) :
    Dense (A : Set X) := by
  classical
  -- `closure (interior A)` is contained in `closure A`.
  have hSub : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  -- Thus `closure A` coincides with `univ`.
  have hClos : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · have hUniv : (Set.univ : Set X) ⊆ closure (A : Set X) := by
        simpa [h] using hSub
      exact hUniv
  -- Translate the closure equality into density.
  exact (Topology.dense_iff_closure_eq_univ (A := A)).2 hClos
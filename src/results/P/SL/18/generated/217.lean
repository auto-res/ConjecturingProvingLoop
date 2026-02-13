

theorem interior_closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    interior (closure (A : Set X)) = Set.univ := by
  -- From the density of `interior A`, obtain that
  -- `interior (closure (interior A)) = univ`.
  have hInt :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_interior_iff_interior_closure_interior_eq_univ (A := A)).1
      hDenseInt
  -- This interior is contained in `interior (closure A)`.
  have hSub :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  -- Hence `univ ⊆ interior (closure A)`.
  have hSubUniv :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hInt] using hSub
  -- Conclude the desired equality by antisymmetry.
  apply Set.Subset.antisymm
  · intro _ _; trivial
  · exact hSubUniv
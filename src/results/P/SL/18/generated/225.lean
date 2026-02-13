

theorem closure_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDenseInt : Dense (interior (A : Set X))) :
    closure (A : Set X) = Set.univ := by
  classical
  -- From the density of `interior A`, obtain a closure equality.
  have hInt : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDenseInt
  -- `closure (interior A)` is contained in `closure A`.
  have hIncl :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (A := A)
  -- Hence `univ ⊆ closure A`.
  have hLeft : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    simpa [hInt] using hIncl
  -- The reverse inclusion is trivial.
  have hRight : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro _ _; trivial
  -- Conclude the proof via antisymmetry.
  exact Set.Subset.antisymm hRight hLeft
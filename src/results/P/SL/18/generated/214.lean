

theorem dense_interior_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior (A : Set X))) :
    Dense (interior (closure (A : Set X))) := by
  -- From the density of `interior A`, obtain a closure equality.
  have hClIntA : closure (interior (A : Set X)) = (Set.univ : Set X) :=
    (Topology.dense_iff_closure_eq_univ
        (A := interior (A : Set X))).1 hDense
  -- `interior A` is contained in `interior (closure A)`.
  have hSubInt :
      interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    Topology.interior_subset_interior_closure (A := A)
  -- Taking closures preserves inclusions.
  have hSubClos :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) :=
    closure_mono hSubInt
  -- Combine the two facts to get the desired closure equality.
  have hClIntClos :
      closure (interior (closure (A : Set X))) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; trivial
    · -- `closure (interior A)` is `univ`, and it sits inside the target closure.
      simpa [hClIntA] using hSubClos
  -- Translate the closure equality back into density.
  exact
    ((Topology.dense_iff_closure_eq_univ
        (A := interior (closure (A : Set X)))).2 hClIntClos)
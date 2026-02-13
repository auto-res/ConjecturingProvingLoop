

theorem Topology.dense_interior_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (interior (closure A)) := by
  intro hDense
  -- The closure of `interior A` is the whole space.
  have hClIntA : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- `interior A` is contained in `interior (closure A)`.
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Taking closures preserves inclusion.
  have hClSubset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono hsubset
  -- Therefore `closure (interior (closure A))` contains `univ`.
  have hUnivSubset :
      (Set.univ : Set X) ⊆ closure (interior (closure A)) := by
    simpa [hClIntA] using hClSubset
  -- The reverse inclusion is trivial.
  have hSubsetUniv :
      closure (interior (closure A)) ⊆ (Set.univ : Set X) := by
    intro x _; simp
  -- Conclude that the closure equals `univ`.
  have hEq :
      closure (interior (closure A)) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSubsetUniv hUnivSubset
  -- Translate the closure equality into a density statement.
  exact (dense_iff_closure_eq).2 hEq
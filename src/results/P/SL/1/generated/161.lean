

theorem Topology.dense_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense A := by
  intro hDenseInt
  -- `closure (interior A)` is the whole space.
  have hIntUniv : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDenseInt.closure_eq
  -- Monotonicity of `closure` gives a useful inclusion.
  have hsubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  -- Show that `closure A` is also the whole space.
  have hAUniv : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · intro x _
      have hx : x ∈ closure (interior A) := by
        simpa [hIntUniv] using (by simp : x ∈ (Set.univ : Set X))
      exact hsubset hx
  -- Conclude density from the closure equality.
  simpa using (dense_iff_closure_eq).2 hAUniv
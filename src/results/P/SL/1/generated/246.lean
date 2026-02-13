

theorem Topology.dense_interior_of_P1_and_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Dense A → Dense (interior A) := by
  intro hP1 hDense
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have hA : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusion.
  have hClosure : closure A ⊆ closure (interior A) := by
    have h := closure_mono hA
    simpa [closure_closure] using h
  -- Because `A` is dense, its closure is `univ`.
  have hUniv : (Set.univ : Set X) ⊆ closure (interior A) := by
    simpa [hDense.closure_eq] using hClosure
  -- Conclude that `closure (interior A) = univ`.
  have hEq : closure (interior A) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · exact hUniv
  -- Translate the closure equality into density.
  exact (dense_iff_closure_eq).2 hEq
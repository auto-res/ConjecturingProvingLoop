

theorem Topology.dense_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (A : Set X) := by
  intro hDenseInt
  -- The closure of `interior A` is the whole space.
  have hInt : closure (interior A) = (Set.univ : Set X) := hDenseInt.closure_eq
  -- `closure (interior A)` is contained in `closure A`.
  have hSub : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence `closure A` contains the whole space.
  have hUnivSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    simpa [hInt] using hSub
  -- The opposite inclusion is trivial, so `closure A = univ`.
  have hClosureA : closure (A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    · exact hUnivSub
  -- Conclude that `A` is dense.
  exact (dense_iff_closure_eq).2 hClosureA
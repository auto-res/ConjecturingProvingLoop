

theorem Topology.P1_of_dense_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (interior A)) (hAB : interior A ⊆ B) :
    Topology.P1 B := by
  -- We prove `closure (interior B) = univ`, from which `P1 B` is immediate.
  have hIntSubset : interior A ⊆ interior B :=
    interior_maximal hAB isOpen_interior
  -- `interior A` is dense, hence its closure is `univ`.
  have hClosureIntA : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Monotonicity of `closure` gives `closure (interior A) ⊆ closure (interior B)`.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure (interior B) := by
    simpa [hClosureIntA] using (closure_mono hIntSubset)
  -- Trivially, `closure (interior B) ⊆ univ`.
  have hSubsetUniv : closure (interior B) ⊆ (Set.univ : Set X) := by
    intro _ _; simp
  -- Combine the inclusions to obtain the desired equality.
  have hClosureIntB : closure (interior B) = (Set.univ : Set X) :=
    Set.Subset.antisymm hSubsetUniv hUnivSubset
  -- Establish `P1 B`.
  unfold Topology.P1
  intro x hxB
  -- Every point belongs to `univ`, hence to `closure (interior B)`.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hClosureIntB] using this
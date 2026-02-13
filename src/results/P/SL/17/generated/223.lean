

theorem Topology.P3_of_dense_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense A) (hAB : A ⊆ B) : Topology.P3 B := by
  -- Unfold the definition of `P3`.
  unfold Topology.P3
  intro x hxB
  -- Since `A` is dense, its closure is the whole space.
  have hClosureA : closure A = (Set.univ : Set X) := hDense.closure_eq
  -- Using monotonicity of `closure`, deduce that `closure B` is also the whole space.
  have hSubset : closure A ⊆ closure B := closure_mono hAB
  have hClosureB : closure B = (Set.univ : Set X) := by
    -- Show the two inclusions needed for set equality.
    apply Set.Subset.antisymm
    ·
      -- `closure B ⊆ univ` is trivial.
      intro _ _; simp
    ·
      -- `univ ⊆ closure B` follows from `closure A = univ` and `closure A ⊆ closure B`.
      simpa [hClosureA] using hSubset
  -- Consequently, the interior of `closure B` is also the whole space.
  have hInteriorB : interior (closure B) = (Set.univ : Set X) := by
    simpa [hClosureB] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Any point of `B` lies in `univ`, hence in `interior (closure B)`.
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hInteriorB] using this
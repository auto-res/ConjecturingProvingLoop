

theorem Topology.P2_of_dense_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hDense : Dense (interior A)) (hAB : interior A ⊆ B) :
    Topology.P2 B := by
  unfold Topology.P2
  intro x hxB
  -- Step 1: `interior A ⊆ interior B`
  have hIntSubset : interior A ⊆ interior B :=
    interior_maximal hAB isOpen_interior
  -- Step 2: `closure (interior A) = univ`
  have hClosureA : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Step 3: `closure (interior B) = univ`
  have hClosureB : closure (interior B) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _ _; simp
    ·
      have h_inc : closure (interior A) ⊆ closure (interior B) :=
        closure_mono hIntSubset
      simpa [hClosureA] using h_inc
  -- Step 4: `interior (closure (interior B)) = univ`
  have hInterior : interior (closure (interior B)) = (Set.univ : Set X) := by
    simpa [hClosureB] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  -- Step 5: Conclude membership
  have : x ∈ (Set.univ : Set X) := by simp
  simpa [hInterior] using this
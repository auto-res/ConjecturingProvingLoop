

theorem dense_interior_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P3 A := by
  intro hDense
  dsimp [Topology.P3]
  intro x hxA
  -- The closure of `interior A` is the whole space.
  have hClosureInt : (closure (interior A) : Set X) = Set.univ := hDense.closure_eq
  -- Hence `closure A` must also be the whole space.
  have hSubset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have hUnivSub : (Set.univ : Set X) ⊆ closure A := by
    simpa [hClosureInt] using hSubset
  have hClosureA : (closure A : Set X) = Set.univ := by
    apply subset_antisymm
    · exact Set.subset_univ _
    · exact hUnivSub
  -- Therefore `interior (closure A)` is also the whole space.
  have hIntClosureA : interior (closure A) = (Set.univ : Set X) :=
    (interior_closure_eq_univ_iff (A := A)).2 hClosureA
  -- Conclude the desired membership.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [hIntClosureA] using this
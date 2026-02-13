

theorem P3_of_compact_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : IsCompact A → Dense (interior A) → Topology.P3 A := by
  intro _ hDense
  intro x hxA
  -- First, `closure (interior A)` is the whole space because `interior A` is dense.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence `closure A` is also the whole space.
  have h_closureA : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; trivial
    ·
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [h_closure_int] using this
  -- Therefore its interior is the whole space.
  have h_interior : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closureA, interior_univ]
  -- Conclude that every point of `A` lies in that interior.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior] using this
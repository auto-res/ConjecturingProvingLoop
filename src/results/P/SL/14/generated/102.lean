

theorem Topology.dense_of_denseInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure (A : Set X))) → Dense (A : Set X) := by
  intro hDense
  -- The closure of `interior (closure A)` is the whole space.
  have h_univ : closure (interior (closure (A : Set X))) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- `closure (interior (closure A))` is contained in `closure A`.
  have h_subset : closure (interior (closure (A : Set X))) ⊆ closure A := by
    have h₀ : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    have h₁ :
        closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
      closure_mono h₀
    simpa [closure_closure] using h₁
  -- Hence `closure A` is the whole space.
  have h_closureA : closure (A : Set X) = (Set.univ : Set X) := by
    have h2 : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_univ] using h_subset
    have h3 : closure A ⊆ (Set.univ : Set X) := by
      intro x hx
      simp
    exact Set.Subset.antisymm h3 h2
  -- Conclude that `A` is dense.
  exact (dense_iff_closure_eq).2 h_closureA
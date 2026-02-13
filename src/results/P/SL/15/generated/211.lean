

theorem denseInterior_closure_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure A)) → Dense A := by
  intro hDense
  -- `closure (interior (closure A))` is the whole space.
  have h_closure_int_univ :
      (closure (interior (closure A) : Set X)) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- We always have `closure (interior (closure A)) ⊆ closure A`.
  have h_subset :
      (closure (interior (closure A) : Set X)) ⊆ closure A :=
    closure_interior_closure_subset_closure (X := X) (A := A)
  -- Hence `closure A = univ`.
  have h_closureA_univ : (closure (A : Set X)) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    · intro x _
      have hx : x ∈ closure (interior (closure A) : Set X) := by
        -- Reinterpret `x ∈ univ` using `h_closure_int_univ`.
        have : x ∈ (Set.univ : Set X) := by
          trivial
        simpa [h_closure_int_univ] using this
      exact h_subset hx
  -- Conclude the density of `A`.
  exact (dense_iff_closure_eq).2 h_closureA_univ
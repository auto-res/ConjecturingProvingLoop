

theorem Topology.dense_interior_closure_iff_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Dense (interior (closure A)) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- `Dense` gives the closure of `interior (closure A)` is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) :=
      hDense.closure_eq
    -- This closure is contained in `closure A`.
    have h_subset : closure (interior (closure A)) ⊆ closure A :=
      Topology.closure_interior_closure_subset_closure (A := A)
    -- Hence `closure A` contains `Set.univ`, so the two sets coincide.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closure_int] using h_subset
    have h_closure_subset : closure A ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm h_closure_subset h_univ_subset
  · intro hClosure
    -- From `closure A = Set.univ`, it follows that `interior (closure A)` is `Set.univ`.
    have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
      simpa [hClosure] using (interior_univ : interior (Set.univ : Set X) = Set.univ)
    -- Consequently, its closure is also `Set.univ`.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int_univ] using
        (closure_univ : closure (Set.univ : Set X) = Set.univ)
    -- Reformulate this equality as the `Dense` property.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closure_int] using this
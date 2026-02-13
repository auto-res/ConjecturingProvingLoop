

theorem Topology.dense_iff_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (interior (closure A)) := by
  constructor
  · intro hDenseA
    -- `closure A` is the whole space.
    have h_closureA : closure A = (Set.univ : Set X) := hDenseA.closure_eq
    -- Hence its interior is also the whole space.
    have h_int : interior (closure A) = (Set.univ : Set X) := by
      simpa [h_closureA] using (interior_univ :
        interior (Set.univ : Set X) = Set.univ)
    -- Consequently, the closure of that interior is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) := by
      simpa [h_int] using (closure_univ :
        closure (Set.univ : Set X) = Set.univ)
    -- Turn the equality into a `Dense` statement.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closure_int] using this
  · intro hDenseInt
    -- The closure of `interior (closure A)` is the whole space.
    have h_closure_int : closure (interior (closure A)) = (Set.univ : Set X) :=
      hDenseInt.closure_eq
    -- `closure (interior (closure A)) ⊆ closure A`.
    have h_subset : closure (interior (closure A)) ⊆ closure A :=
      Topology.closure_interior_closure_subset_closure (A := A)
    -- Therefore, `closure A` is also the whole space.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_closure_int] using h_subset
    have h_closureA : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _x _hx; simp
      · exact h_univ_subset
    -- Convert the equality into a `Dense` statement for `A`.
    intro x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h_closureA] using this
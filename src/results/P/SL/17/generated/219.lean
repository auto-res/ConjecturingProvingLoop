

theorem Topology.dense_iff_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ closure (interior (closure A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have h_closure : closure A = (Set.univ : Set X) := hDense.closure_eq
    calc
      closure (interior (closure A))
          = closure (interior (Set.univ : Set X)) := by
              simpa [h_closure]
      _ = closure (Set.univ : Set X) := by
          simpa [interior_univ]
      _ = (Set.univ : Set X) := by
          simpa using closure_univ
  · intro hEq
    -- First, deduce `closure A = Set.univ`.
    have h_closureA_univ : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro x _; simp
      ·
        have h_subset : closure (interior (closure A)) ⊆ closure A :=
          Topology.closure_interior_closure_subset_closure (A := A)
        simpa [hEq] using h_subset
    -- Turn the equality into the `Dense` property.
    have hDense : Dense A := by
      intro x
      have : (x : X) ∈ (Set.univ : Set X) := by simp
      simpa [h_closureA_univ] using this
    exact hDense
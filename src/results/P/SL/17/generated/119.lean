

theorem Topology.dense_iff_dense_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ Dense (closure A) := by
  constructor
  · intro hDense
    have h_eq : closure A = (Set.univ : Set X) := hDense.closure_eq
    -- Deduce density of `closure A`.
    have hDenseClosure : Dense (closure A) := by
      intro x
      have hx : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [closure_closure, h_eq] using hx
    exact hDenseClosure
  · intro hDenseClosure
    have h_eq : closure A = (Set.univ : Set X) := by
      -- `closure (closure A) = Set.univ` implies `closure A = Set.univ`.
      simpa [closure_closure] using hDenseClosure.closure_eq
    -- Deduce density of `A`.
    have hDense : Dense A := by
      intro x
      have hx : (x : X) ∈ (Set.univ : Set X) := by
        simp
      simpa [h_eq] using hx
    exact hDense


theorem dense_closure_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ Dense A := by
  constructor
  · intro hDenseClosure
    -- From the density of `closure A`, we get `closure (closure A) = univ`.
    have h₁ : closure (closure A : Set X) = (Set.univ : Set X) := by
      simpa using hDenseClosure.closure_eq
    -- Using `closure_closure`, deduce `closure A = univ`, hence `Dense A`.
    have h₂ : closure (A : Set X) = (Set.univ : Set X) := by
      simpa [closure_closure] using h₁
    exact (dense_iff_closure_eq (s := A)).2 h₂
  · intro hDenseA
    -- The closure of a dense set is dense.
    exact dense_closure_of_dense (X := X) (A := A) hDenseA
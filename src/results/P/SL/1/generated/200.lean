

theorem Topology.dense_closure_iff_dense
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure A) ↔ Dense A := by
  constructor
  · intro hDenseCl
    -- `Dense (closure A)` gives `closure (closure A) = univ`.
    have hEq : closure (closure A) = (Set.univ : Set X) := hDenseCl.closure_eq
    -- Use idempotence of `closure` to simplify.
    have hEq' : closure A = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq
    -- Conclude that `A` is dense.
    exact (dense_iff_closure_eq).2 hEq'
  · intro hDenseA
    -- `Dense A` yields `closure A = univ`.
    have hEq : closure A = (Set.univ : Set X) := hDenseA.closure_eq
    -- Therefore `closure (closure A) = univ`.
    have hEq' : closure (closure A) = (Set.univ : Set X) := by
      simpa [closure_closure, hEq, closure_univ]
    -- Conclude that `closure A` is dense.
    exact (dense_iff_closure_eq).2 hEq'
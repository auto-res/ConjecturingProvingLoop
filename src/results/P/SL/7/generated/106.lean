

theorem Topology.closureInteriorClosure_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (A : Set X))) ⊆ closure (A : Set X) := by
  -- `interior (closure A)` is contained in `closure A`.
  have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
    interior_subset
  -- Taking closures preserves the inclusion.
  have hClosure :
      closure (interior (closure (A : Set X))) ⊆ closure (closure (A : Set X)) :=
    closure_mono hSub
  -- Simplify the right-hand side using idempotency of `closure`.
  simpa [closure_closure] using hClosure
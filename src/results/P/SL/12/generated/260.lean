

theorem Topology.closure_subset_closure_of_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (A : Set X) ⊆ closure (interior B)) :
    closure (A : Set X) ⊆ closure (interior B) := by
  -- Taking closures preserves the given inclusion.
  have h₁ : closure (A : Set X) ⊆ closure (closure (interior B)) :=
    closure_mono h
  -- Simplify the right‐hand side using idempotence of `closure`.
  simpa [closure_closure] using h₁
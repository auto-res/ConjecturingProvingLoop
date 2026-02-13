

theorem Topology.closure_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hSub : (A : Set X) ⊆ closure (B : Set X))
    (hClosed : IsClosed (B : Set X)) :
    closure (A : Set X) ⊆ (B : Set X) := by
  -- `closure A` is contained in the closure of `closure B`.
  have h₁ : closure (A : Set X) ⊆ closure (closure (B : Set X)) :=
    closure_mono hSub
  -- Since `B` is closed, `closure B = B`.
  simpa [closure_closure, hClosed.closure_eq] using h₁
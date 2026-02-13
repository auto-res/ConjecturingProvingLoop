

theorem closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → closure A ⊆ closure (interior A) := by
  intro hP1
  -- `P1` gives the inclusion `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions.
  have hClos : closure (A : Set X) ⊆ closure (closure (interior A)) :=
    closure_mono hSub
  -- Simplify using idempotence of `closure`.
  simpa [closure_closure] using hClos
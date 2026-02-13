

theorem Topology.P1_implies_closure_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure A ⊆ closure (interior (closure A)) := by
  intro hP1
  -- First, `P1 A` gives the inclusion `A ⊆ closure (interior (closure A))`.
  have hSub : (A : Set X) ⊆ closure (interior (closure A)) :=
    Topology.P1_implies_subset_closure_interior_closure (A := A) hP1
  -- Taking closures preserves inclusions.
  have hClSub :
      closure (A : Set X) ⊆ closure (closure (interior (closure A))) :=
    closure_mono hSub
  -- Simplify the right‐hand side using idempotence of `closure`.
  simpa [closure_closure] using hClSub


theorem Topology.interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆ closure A := by
  intro x hx
  -- `x` lies in the closure of `interior (closure A)`.
  have hx₁ : x ∈ closure (interior (closure (A : Set X))) :=
    interior_subset hx
  -- `interior (closure A)` itself is contained in `closure A`.
  have hIntSub : (interior (closure (A : Set X)) : Set X) ⊆ closure A := by
    intro y hy
    exact interior_subset hy
  -- Taking closures preserves inclusions.
  have hClSub :
      closure (interior (closure (A : Set X))) ⊆ closure (closure (A : Set X)) :=
    closure_mono hIntSub
  -- Simplify the right‐hand closure.
  have hSub : (closure (interior (closure (A : Set X))) : Set X) ⊆ closure A := by
    simpa [closure_closure] using hClSub
  exact hSub hx₁


theorem Topology.P1_implies_closure_frontier_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (frontier (A : Set X)) ⊆ closure (interior A) := by
  intro hP1
  -- Step 1: `frontier A` is contained in `closure A`, and `closure A`
  -- is contained in `closure (interior A)` thanks to `P1`.
  have hFrontSub :
      (frontier (A : Set X) : Set X) ⊆ closure (interior A) := by
    have h₁ :
        (frontier (A : Set X) : Set X) ⊆ closure (A : Set X) :=
      Topology.frontier_subset_closure (A := A)
    have h₂ :
        closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
    exact h₁.trans h₂
  -- Step 2: taking closures preserves inclusions; simplify the right‐hand side.
  have hCl :
      closure (frontier (A : Set X)) ⊆ closure (closure (interior A)) :=
    closure_mono hFrontSub
  simpa [closure_closure] using hCl
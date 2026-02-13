

theorem P1_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  dsimp [Topology.P1] at *
  intro x hx
  -- Step 1: From `P1_closure_subset`, points of `closure A` lie in `closure (interior A)`.
  have h₁ : x ∈ closure (interior A) := by
    have hsubset : closure (A : Set X) ⊆ closure (interior A) :=
      Topology.P1_closure_subset (X := X) (A := A) hA
    exact hsubset hx
  -- Step 2: `closure (interior A)` is contained in `closure (interior (closure A))`.
  have hsubset₂ : closure (interior A) ⊆
      closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_subset_closure_interior_closure (X := X) A
  -- Combine the two inclusions.
  exact hsubset₂ h₁
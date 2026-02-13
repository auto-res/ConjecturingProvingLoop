

theorem P1_implies_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → closure (interior (closure A)) = closure A := by
  intro hP1
  -- From `P1`, we have `closure A = closure (interior A)`.
  have h_cl : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- We prove the desired equality by showing both inclusions.
  apply Set.Subset.antisymm
  · -- `closure (interior (closure A)) ⊆ closure A`
    exact
      Topology.closure_interior_closure_subset_closure
        (X := X) (A := A)
  · -- `closure A ⊆ closure (interior (closure A))`
    -- Rewrite the left‐hand side via `h_cl`.
    have h_sub :
        closure (interior A) ⊆ closure (interior (closure A)) := by
      have h_int_sub :
          interior A ⊆ interior (closure A) :=
        Topology.interior_subset_interior_closure (X := X) (A := A)
      exact closure_mono h_int_sub
    simpa [h_cl] using h_sub
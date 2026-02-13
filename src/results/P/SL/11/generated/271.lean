

theorem closure_eq_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- First, recall the equality furnished by `P1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- Establish the two inclusions.
  apply subset_antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hsubset : closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_interior_subset_closure_interior_closure (A := A)
    simpa [hEq] using hsubset
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hsubset : interior (closure A) ⊆ closure A := interior_subset
    have hclosure :
        closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure
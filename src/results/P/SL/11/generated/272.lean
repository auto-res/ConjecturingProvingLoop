

theorem closure_eq_closure_interior_closure_of_P1_alt
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- First, recall the closure equality provided by `P1`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- Establish the two subset inclusions.
  apply Set.Subset.antisymm
  ·
    -- `closure A ⊆ closure (interior (closure A))`
    have hSubInt : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    have hSub : closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_mono hSubInt
    simpa [hEq] using hSub
  ·
    -- `closure (interior (closure A)) ⊆ closure A`
    have hSubInt : (interior (closure A) : Set X) ⊆ closure A :=
      interior_subset
    have hSub : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hSubInt
    simpa [closure_closure] using hSub
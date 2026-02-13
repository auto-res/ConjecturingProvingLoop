

theorem closure_eq_closure_interior_closure_of_P1'
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P1 A) :
    closure A = closure (interior (closure A)) := by
  -- From `P1`, we already have `closure A = closure (interior A)`.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) h
  -- We establish the desired equality via double inclusion.
  apply subset_antisymm
  ·
    -- First inclusion: `closure A ⊆ closure (interior (closure A))`.
    have h₁ : closure (interior A) ⊆ closure (interior (closure A)) := by
      -- Since `A ⊆ closure A`, we have `interior A ⊆ interior (closure A)`.
      have hSub : (interior A : Set X) ⊆ interior (closure A) :=
        interior_mono (subset_closure : (A : Set X) ⊆ closure A)
      -- Taking closures preserves inclusions.
      exact closure_mono hSub
    simpa [hEq] using h₁
  ·
    -- Second inclusion: `closure (interior (closure A)) ⊆ closure A`.
    have h₂ : (interior (closure A) : Set X) ⊆ closure A := interior_subset
    -- Again, taking closures preserves inclusions and `closure (closure A) = closure A`.
    simpa [closure_closure] using closure_mono h₂
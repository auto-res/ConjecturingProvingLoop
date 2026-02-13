

theorem closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P3 A) :
    closure A = closure (interior (closure A)) := by
  apply subset_antisymm
  ·
    -- From `P3`, we have `A ⊆ interior (closure A)`.
    have h₁ : (A : Set X) ⊆ interior (closure A) := h
    -- Taking closures yields the desired inclusion.
    simpa using (closure_mono h₁)
  ·
    -- The interior of a set is always contained in the set itself.
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    -- Taking closures on both sides (and simplifying) gives the reverse inclusion.
    simpa [closure_closure] using (closure_mono h₂)
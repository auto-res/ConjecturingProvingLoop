

theorem interior_closure_interior_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    interior (closure (interior (A : Set X))) = interior A := by
  apply le_antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    -- Since `interior A ⊆ A` and `A` is closed, the closure of `interior A`
    -- is contained in `A`.
    have hsubset : closure (interior (A : Set X)) ⊆ A := by
      have h₁ : (interior (A : Set X) : Set X) ⊆ A := interior_subset
      have h₂ : closure (interior (A : Set X)) ⊆ closure A := closure_mono h₁
      simpa [hA_closed.closure_eq] using h₂
    -- Applying monotonicity of `interior` yields the desired inclusion.
    exact interior_mono hsubset
  · -- `interior A ⊆ interior (closure (interior A))`
    -- `interior A` is open and contained in `closure (interior A)`.
    have hsubset : (interior (A : Set X) : Set X) ⊆ closure (interior (A : Set X)) :=
      subset_closure
    have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
    -- Use the maximality property of `interior`.
    exact interior_maximal hsubset h_open
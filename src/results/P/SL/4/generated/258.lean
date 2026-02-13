

theorem frontier_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (interior A) ⊆ closure A := by
  intro x hx
  -- Unpack the definition of `frontier (interior A)`.
  rcases hx with ⟨hx_cl, _hx_not_int⟩
  -- `closure (interior A)` is contained in `closure A` because `interior A ⊆ A`.
  have h_sub : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  exact h_sub hx_cl
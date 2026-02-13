

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (A : Set X))) ⊆ closure (A : Set X) := by
  intro x hx
  -- From `hx`, we know `x` lies in the closure of `interior A`.
  have hx_closure_int : (x : X) ∈ closure (interior (A : Set X)) :=
    interior_subset (s := closure (interior (A : Set X))) hx
  -- `closure (interior A)` is contained in `closure A`.
  have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset (s := A))
  -- Combining the facts yields the desired inclusion.
  exact h_subset hx_closure_int
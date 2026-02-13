

theorem closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure (A : Set X))) ⊆
      closure (interior (closure (B : Set X))) := by
  -- `A ⊆ B` implies `closure A ⊆ closure B`.
  have h_cl : closure (A : Set X) ⊆ closure (B : Set X) :=
    closure_mono hAB
  -- Applying `interior_mono` to the previous inclusion.
  have h_int : interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h_cl
  -- Taking closures preserves inclusions.
  exact closure_mono h_int
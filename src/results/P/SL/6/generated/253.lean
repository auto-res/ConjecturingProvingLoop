

theorem closure_inter_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    (closure (A : Set X) ∩ interior (closure A))
      = interior (closure A) := by
  -- `interior (closure A)` is contained in `closure A`.
  have h : interior (closure (A : Set X)) ⊆ closure A := interior_subset
  -- Use the set-theoretic lemma `inter_eq_right` to obtain the equality.
  exact Set.inter_eq_right.mpr h
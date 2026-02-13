

theorem Topology.eq_empty_of_closure_eq_empty {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = (∅ : Set X)) : A = (∅ : Set X) := by
  -- We show the two inclusions to obtain the desired set equality.
  apply Set.Subset.antisymm
  · -- `A ⊆ ∅`
    intro x hxA
    -- Every element of `A` lies in `closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Rewrite using `h : closure A = ∅`.
    simpa [h] using hx_closure
  · -- `∅ ⊆ A` is trivial.
    intro x hxEmpty
    exact False.elim hxEmpty
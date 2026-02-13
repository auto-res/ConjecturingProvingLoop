

theorem Topology.interior_eq_interior_closure_diff_frontier {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) =
      interior (closure (A : Set X)) \ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxIntA
    -- `x` lies in the interior of `closure A` because `A ⊆ closure A`.
    have hxIntCl : x ∈ interior (closure (A : Set X)) := by
      have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      exact (interior_mono hSub) hxIntA
    -- Points of `interior A` are never in the frontier of `A`.
    have hxNotFront : x ∉ frontier (A : Set X) := by
      intro hxFront
      exact hxFront.2 hxIntA
    exact And.intro hxIntCl hxNotFront
  · rintro ⟨hxIntCl, hxNotFront⟩
    -- We show that `x ∈ interior A`; otherwise we obtain a contradiction.
    by_contra hNotIntA
    -- `x` lies in `closure A` because it is in `interior (closure A)`.
    have hxClA : x ∈ closure (A : Set X) := interior_subset hxIntCl
    -- Hence `x` would be in the frontier of `A`, contradicting `hxNotFront`.
    have hxFront : x ∈ frontier (A : Set X) := And.intro hxClA hNotIntA
    exact hxNotFront hxFront
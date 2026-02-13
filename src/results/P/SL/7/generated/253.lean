

theorem Topology.interiorClosure_union_eq_union_of_open_closures
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure (B : Set X))) :
    interior (closure (A ∪ B : Set X)) =
      closure (A : Set X) ∪ closure (B : Set X) := by
  apply Set.Subset.antisymm
  · -- `⊆`: every point in the interior of the closure of `A ∪ B`
    --       belongs to `closure A ∪ closure B`.
    intro x hx
    have : (x : X) ∈ closure (A ∪ B : Set X) := interior_subset hx
    simpa [closure_union] using this
  · -- `⊇`: each point in `closure A ∪ closure B`
    --       lies in the interior of the closure of `A ∪ B`.
    intro x hx
    cases hx with
    | inl hxA =>
        -- Handle the case `x ∈ closure A`.
        have hSub : (closure (A : Set X)) ⊆ closure (A ∪ B : Set X) := by
          apply closure_mono
          exact Set.subset_union_left
        have hIncl :
            closure (A : Set X) ⊆ interior (closure (A ∪ B : Set X)) :=
          interior_maximal hSub hA
        exact hIncl hxA
    | inr hxB =>
        -- Handle the case `x ∈ closure B`.
        have hSub : (closure (B : Set X)) ⊆ closure (A ∪ B : Set X) := by
          apply closure_mono
          exact Set.subset_union_right
        have hIncl :
            closure (B : Set X) ⊆ interior (closure (A ∪ B : Set X)) :=
          interior_maximal hSub hB
        exact hIncl hxB
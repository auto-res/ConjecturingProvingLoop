

theorem Topology.frontier_eq_closure_inter_closure_compl {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) = closure (A : Set X) ∩ closure (Aᶜ : Set X) := by
  -- We prove the equality by mutual inclusion.
  apply Set.Subset.antisymm
  · -- `⊆` : every frontier point lies in both closures.
    intro x hx
    exact
      And.intro
        (Topology.frontier_subset_closure (A := A) hx)
        (Topology.frontier_subset_closure_compl (A := A) hx)
  · -- `⊇` : a point in the intersection of the closures lies in the frontier.
    rintro x ⟨hxClA, hxClAc⟩
    -- We first show that `x ∉ interior A`.
    have hNotInt : x ∉ interior (A : Set X) := by
      intro hxInt
      -- Because `x ∈ interior A`, the open set `interior A`
      -- is a neighbourhood of `x` contained in `A`.
      -- This contradicts `x ∈ closure Aᶜ`, which requires every neighbourhood
      -- of `x` to meet `Aᶜ`.
      have hNonempty :
          ((interior (A : Set X)) ∩ (Aᶜ : Set X)).Nonempty :=
        (mem_closure_iff.1 hxClAc) (interior (A : Set X)) isOpen_interior hxInt
      rcases hNonempty with ⟨y, hyInt, hyAc⟩
      have hInA : (y : X) ∈ (A : Set X) := interior_subset hyInt
      have hNotInA : (y : X) ∉ (A : Set X) := by
        simpa using hyAc
      exact hNotInA hInA
    -- Having `x ∈ closure A` and `x ∉ interior A`, we are in the frontier.
    exact And.intro hxClA hNotInt
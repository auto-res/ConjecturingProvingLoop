

theorem Topology.frontier_subset_compl_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → frontier (A : Set X) ⊆ (Aᶜ : Set X) := by
  intro hOpen x hxFront
  -- Rewrite the frontier of an open set.
  have hEq := Topology.frontier_eq_closure_diff_self_of_isOpen (A := A) hOpen
  have hxDiff : x ∈ closure (A : Set X) \ (A : Set X) := by
    simpa [hEq] using hxFront
  -- Extract the fact `x ∉ A`, hence `x ∈ Aᶜ`.
  rcases hxDiff with ⟨_, hxNotA⟩
  simpa [Set.mem_compl] using hxNotA
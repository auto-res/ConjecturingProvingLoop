

theorem Topology.frontier_subset_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (Aᶜ : Set X) := by
  intro x hxFront
  rcases hxFront with ⟨hxClA, hxNotIntA⟩
  by_cases hmem : x ∈ closure (Aᶜ : Set X)
  · exact hmem
  ·
    -- `x` lies in the open set `U = (closure Aᶜ)ᶜ`.
    have hxInU : x ∈ (closure (Aᶜ : Set X))ᶜ := by
      have : x ∉ closure (Aᶜ : Set X) := hmem
      simpa [Set.mem_compl] using this
    have hOpenU : IsOpen ((closure (Aᶜ : Set X))ᶜ) :=
      (isClosed_closure (s := (Aᶜ : Set X))).isOpen_compl
    -- Show that `U ⊆ A`.
    have hU_sub_A : ((closure (Aᶜ : Set X))ᶜ : Set X) ⊆ A := by
      intro y hyU
      by_contra hNotA
      -- From `y ∉ A`, deduce `y ∈ Aᶜ`.
      have hyInCompl : (y : X) ∈ (Aᶜ : Set X) := by
        simpa [Set.mem_compl] using hNotA
      -- Hence `y ∈ closure Aᶜ`, contradicting `hyU`.
      have hyInClos : y ∈ closure (Aᶜ : Set X) := subset_closure hyInCompl
      have : y ∉ closure (Aᶜ : Set X) := by
        simpa [Set.mem_compl] using hyU
      exact (this hyInClos).elim
    -- `U` is an open neighbourhood of `x` contained in `A`, so `x ∈ interior A`.
    have hxIntA : x ∈ interior (A : Set X) := by
      have hU_sub_intA :
          ((closure (Aᶜ : Set X))ᶜ : Set X) ⊆ interior (A : Set X) :=
        interior_maximal hU_sub_A hOpenU
      exact hU_sub_intA hxInU
    exact (hxNotIntA hxIntA).elim
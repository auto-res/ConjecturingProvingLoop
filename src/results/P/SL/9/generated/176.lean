

theorem Set.compl_compl {α : Type*} (s : Set α) : (sᶜ)ᶜ = s := by
  ext x
  simp

theorem Set.disjoint_compl_left {α : Type*} (s : Set α) : Disjoint s sᶜ := by
  exact (Set.disjoint_left).2 (by
    intro x hxS hxSc
    exact hxSc hxS)
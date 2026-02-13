

theorem Set.subset_closure {X : Type*} [TopologicalSpace X] {s : Set X} :
    s ⊆ closure s := by
  intro x hx
  have h : ∀ o : Set X, IsOpen o → x ∈ o → (o ∩ s).Nonempty := by
    intro o ho hxo
    exact ⟨x, hxo, hx⟩
  exact (mem_closure_iff).2 h
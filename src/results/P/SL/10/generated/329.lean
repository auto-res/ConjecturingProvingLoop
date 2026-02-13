

theorem Topology.closure_diff_subset_closure_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ A ⊆ closure (Aᶜ) := by
  intro x hx
  rcases hx with ⟨_, hxNotA⟩
  -- To show `x ∈ closure (Aᶜ)`, use the neighbourhood criterion.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- The point `x` itself witnesses the non‐emptiness of `U ∩ Aᶜ`.
  exact ⟨x, And.intro hxU hxNotA⟩
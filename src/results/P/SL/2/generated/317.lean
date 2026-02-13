

theorem Topology.closure_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) ∪ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  -- We prove both inclusions separately.
  apply Set.Subset.antisymm
  · intro _; simp
  · intro x _
    by_cases h : x ∈ (A : Set X)
    ·
      have hx : x ∈ closure (A : Set X) := subset_closure h
      exact Or.inl hx
    ·
      have hxComp : x ∈ (Aᶜ : Set X) := h
      have hx : x ∈ closure (Aᶜ : Set X) := subset_closure hxComp
      exact Or.inr hx


theorem Topology.closure_union_closure_compl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∪ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    by_cases hx : x ∈ closure (A : Set X)
    · exact Or.inl hx
    · -- Otherwise, `x` is outside `closure A`; in particular, it is outside `A`.
      have hxAcomp : (x : X) ∈ (Aᶜ : Set X) := by
        have : x ∉ (A : Set X) := by
          intro hxA
          have : (x : X) ∈ closure (A : Set X) := subset_closure hxA
          exact hx this
        simpa using this
      exact Or.inr (subset_closure hxAcomp)


theorem Topology.closureCompl_union_self {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (Aᶜ) ∪ A = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x ∈ A
    · exact Or.inr hx
    ·
      have hx_compl : x ∈ (Aᶜ : Set X) := hx
      have hx_closure : x ∈ closure (Aᶜ : Set X) := subset_closure hx_compl
      exact Or.inl hx_closure
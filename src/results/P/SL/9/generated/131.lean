

theorem Topology.closure_union_closure_compl {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h_cl : x ∈ closure A
    · exact Or.inl h_cl
    · -- `x ∉ closure A`; we show `x ∈ closure (Aᶜ)`
      have hAcomp : x ∈ Aᶜ := by
        by_cases hA : x ∈ A
        · have : x ∈ closure A := Set.subset_closure hA
          exact (h_cl this).elim
        · simpa [Set.compl_def] using hA
      exact Or.inr (Set.subset_closure hAcomp)
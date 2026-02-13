

theorem Topology.interior_union_closureCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hx : x ∈ interior A
    · exact Or.inl hx
    ·
      have hx_comp : x ∈ (interior A)ᶜ := hx
      have h_eq : (closure (Aᶜ) : Set X) = (interior A)ᶜ :=
        Topology.closure_compl_eq_compl_interior (A := A)
      have hx_closure : x ∈ closure (Aᶜ) := by
        simpa [h_eq] using hx_comp
      exact Or.inr hx_closure
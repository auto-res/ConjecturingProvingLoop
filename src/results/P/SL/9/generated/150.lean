

theorem Topology.closure_union_interiorCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ∪ interior (Aᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hx : x ∈ closure A
    · exact Or.inl hx
    ·
      have hx_interior : x ∈ interior (Aᶜ) := by
        have h_eq := Topology.interior_compl_eq_compl_closure (A := A)
        have h_mem : x ∈ (closure A)ᶜ := hx
        simpa [h_eq] using h_mem
      exact Or.inr hx_interior
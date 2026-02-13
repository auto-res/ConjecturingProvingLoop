

theorem Topology.boundary_subset_compl_iff_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) \ interior A ⊆ Aᶜ ↔ IsOpen A := by
  classical
  constructor
  · intro h_boundary
    -- We show `A` equals its interior.
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · intro x hxA
        by_cases hx_int : x ∈ interior A
        · exact hx_int
        ·
          -- Otherwise `x` lies in the boundary, contradicting `h_boundary`.
          have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
          have hx_bd : x ∈ closure (A : Set X) \ interior A := ⟨hx_cl, hx_int⟩
          have hx_compl : x ∈ (Aᶜ : Set X) := h_boundary hx_bd
          exact (hx_compl hxA).elim
    simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
  · intro hA_open
    intro x hx_bd
    -- Using `interior A = A` for open sets.
    have h_int_eq : interior A = A := hA_open.interior_eq
    have hx_not_int : x ∉ interior A := hx_bd.2
    have hx_not_A : x ∉ A := by
      simpa [h_int_eq] using hx_not_int
    simpa using hx_not_A
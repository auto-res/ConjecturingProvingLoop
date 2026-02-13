

theorem P3_compl_of_closed' {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P3 (Aᶜ) := by
  intro hClosed hP3A
  -- touch `hP3A` to avoid an unused-argument warning
  have _ := hP3A
  -- the complement of a closed set is open
  have hOpen : IsOpen (Aᶜ : Set X) := (isOpen_compl_iff).2 hClosed
  -- open sets satisfy `P3`
  exact P3_of_open (X := X) (A := Aᶜ) hOpen

theorem P2_filter_basis {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ s, IsOpen s ∧ x ∈ s ∧ s ⊆ A) → P2 A := by
  intro h
  intro x hxA
  rcases h x hxA with ⟨s, hs_open, hx_s, hs_sub⟩
  -- `s` is an open subset of `A`, hence contained in `interior A`
  have hs_sub_int : s ⊆ interior A := by
    apply interior_maximal
    · exact hs_sub
    · exact hs_open
  -- therefore `x ∈ interior A`
  have hx_intA : x ∈ interior A := hs_sub_int hx_s
  -- `interior A` is an open subset of `closure (interior A)`
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact h_subset hx_intA


theorem Topology.interior_diff_eq_interior_diff_closed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_closed : IsClosed (B : Set X)) :
    interior (A \ B : Set X) = interior A \ B := by
  ext x
  constructor
  · intro hx
    -- From `x ∈ interior (A \ B)` we get `x ∈ interior A`.
    have hxIntA : (x : X) ∈ interior A := by
      have h_subset : (A \ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono h_subset) hx
    -- And we also have `x ∉ B`.
    have hxNotB : (x : X) ∉ B := by
      have : (x : X) ∈ A \ B :=
        (interior_subset : interior (A \ B : Set X) ⊆ A \ B) hx
      exact this.2
    exact And.intro hxIntA hxNotB
  · rintro ⟨hxIntA, hxNotB⟩
    -- Consider the open neighbourhood `U = interior A ∩ Bᶜ` of `x`.
    have hU_open : IsOpen (interior A ∩ Bᶜ) :=
      IsOpen.inter isOpen_interior hB_closed.isOpen_compl
    have hxU : (x : X) ∈ (interior A ∩ Bᶜ : Set X) :=
      And.intro hxIntA hxNotB
    -- `U` is contained in `A \ B`.
    have hU_subset : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
      intro y hy
      rcases hy with ⟨hyIntA, hyNotB⟩
      have hyA : (y : X) ∈ A := interior_subset hyIntA
      exact And.intro hyA hyNotB
    -- Hence `x ∈ interior (A \ B)`.
    have hU_interior :
        (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B : Set X) :=
      interior_maximal hU_subset hU_open
    exact hU_interior hxU


theorem Topology.diff_closure_subset_interior_diff
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A \ closure B ⊆ interior (A \ B) := by
  intro x hx
  rcases hx with ⟨hxIntA, hxNotClB⟩
  -- `interior A` is open, and so is the complement of `closure B`.
  have h_open₁ : IsOpen (interior A) := isOpen_interior
  have h_open₂ : IsOpen ((closure B)ᶜ) :=
    (isClosed_closure : IsClosed (closure B)).isOpen_compl
  let S : Set X := interior A ∩ (closure B)ᶜ
  have hS_open : IsOpen S := h_open₁.inter h_open₂
  have hxS : x ∈ S := And.intro hxIntA hxNotClB
  -- Show that `S ⊆ A \ B`.
  have h_subset : S ⊆ A \ B := by
    intro y hy
    rcases hy with ⟨hyIntA, hyNotClB⟩
    have hyA : y ∈ A := interior_subset hyIntA
    have hyNotB : y ∉ B := by
      intro hyB
      have : y ∈ closure B := subset_closure hyB
      exact hyNotClB this
    exact And.intro hyA hyNotB
  -- Apply the maximality property of the interior.
  have : x ∈ interior (A \ B) :=
    (interior_maximal h_subset hS_open) hxS
  exact this


theorem Topology.interior_diff_closure_subset_interior_diff {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) \ closure B ⊆ interior (A \ B : Set X) := by
  intro x hx
  rcases hx with ⟨hx_intA, hx_not_clB⟩
  -- Define two auxiliary open sets.
  have hU_open : IsOpen (interior (A : Set X)) := isOpen_interior
  have hV_open : IsOpen ((closure B)ᶜ : Set X) := by
    simpa using (isClosed_closure (A := B)).isOpen_compl
  -- Their intersection is an open neighbourhood of `x`.
  have hW_open :
      IsOpen (interior (A : Set X) ∩ (closure B)ᶜ : Set X) :=
    hU_open.inter hV_open
  have hxW :
      x ∈ (interior (A : Set X) ∩ (closure B)ᶜ : Set X) :=
    And.intro hx_intA hx_not_clB
  -- Show that this neighbourhood is contained in `A \ B`.
  have hW_subset :
      (interior (A : Set X) ∩ (closure B)ᶜ : Set X) ⊆ (A \ B : Set X) := by
    intro y hy
    have hyA : y ∈ A :=
      (interior_subset : interior (A : Set X) ⊆ A) hy.1
    have hy_notB : y ∉ B := by
      intro hBy
      have : y ∈ closure B := subset_closure hBy
      exact hy.2 this
    exact And.intro hyA hy_notB
  -- Apply maximality of the interior to deduce the claim.
  exact
    (interior_maximal hW_subset hW_open) hxW
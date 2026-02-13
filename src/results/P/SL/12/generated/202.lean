

theorem Topology.interior_diff_closed_eq {X : Type*} [TopologicalSpace X]
    {A C : Set X} (hC : IsClosed (C : Set X)) :
    interior (A \ C : Set X) = interior A \ C := by
  -- First, prove the inclusion `⊆`.
  have h₁ : interior (A \ C : Set X) ⊆ interior A \ C := by
    intro x hx
    -- From `x ∈ interior (A \ C)` we get `x ∈ interior A`.
    have hxA : x ∈ interior A :=
      (interior_mono (Set.diff_subset : (A \ C : Set X) ⊆ A)) hx
    -- And `x ∉ C`, since `x` actually lies in `A \ C`.
    have hxNC : x ∉ C := by
      have : x ∈ (A \ C : Set X) := interior_subset hx
      exact this.2
    exact And.intro hxA hxNC
  -- Next, prove the inclusion `⊇`.
  have h₂ : interior A \ C ⊆ interior (A \ C : Set X) := by
    intro x hx
    rcases hx with ⟨hxA, hxNC⟩
    -- Construct an open neighbourhood of `x` contained in `A \ C`.
    have h_open_int : IsOpen (interior (A : Set X)) := isOpen_interior
    have h_open_compl : IsOpen (Cᶜ : Set X) := hC.isOpen_compl
    have h_open : IsOpen (interior A ∩ Cᶜ : Set X) :=
      h_open_int.inter h_open_compl
    have hx_in : x ∈ (interior A ∩ Cᶜ : Set X) := And.intro hxA hxNC
    -- Show this neighbourhood is contained in `A \ C`.
    have h_subset :
        (interior A ∩ Cᶜ : Set X) ⊆ (A \ C : Set X) := by
      intro y hy
      have hyA : y ∈ A := (interior_subset : interior A ⊆ A) hy.1
      exact And.intro hyA hy.2
    -- Apply maximality of the interior.
    have h_interior :
        (interior A ∩ Cᶜ : Set X) ⊆ interior (A \ C : Set X) :=
      interior_maximal h_subset h_open
    exact h_interior hx_in
  -- Combine the two inclusions.
  exact Set.Subset.antisymm h₁ h₂


theorem closure_inter_closure_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Membership in `closure A` comes from the left inclusion.
  have hA : x ∈ closure A := by
    have hsubset : (A ∩ closure B : Set X) ⊆ A := Set.inter_subset_left
    exact (closure_mono hsubset) hx
  -- Membership in `closure B` comes from the right inclusion.
  have hB : x ∈ closure B := by
    have hsubset : (A ∩ closure B : Set X) ⊆ closure B := Set.inter_subset_right
    have hcl : closure (A ∩ closure B) ⊆ closure (closure B) :=
      closure_mono hsubset
    have : x ∈ closure (closure B) := hcl hx
    simpa [closure_closure] using this
  exact ⟨hA, hB⟩
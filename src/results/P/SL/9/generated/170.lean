

theorem Topology.closure_inter_closureCompl_eq_closure_diff_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) ∩ closure (Aᶜ) = closure A \ interior A := by
  -- First, rewrite `closure (Aᶜ)` using a previously proved lemma.
  have h : closure (Aᶜ : Set X) = (interior A)ᶜ :=
    Topology.closure_compl_eq_compl_interior (A := A)
  -- Reduce the goal to a set‐theoretic identity.
  calc
    closure A ∩ closure (Aᶜ) = closure A ∩ (interior A)ᶜ := by
      simpa [h]
    _ = closure A \ interior A := by
      -- Both sides are equal to `closure A ∩ (interior A)ᶜ`.
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, by
          -- `x ∈ (interior A)ᶜ` means `x ∉ interior A`.
          simpa using hx.2⟩
      · intro hx
        exact ⟨hx.1, by
          -- `x ∉ interior A` means `x ∈ (interior A)ᶜ`.
          simpa using hx.2⟩
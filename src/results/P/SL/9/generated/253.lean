

theorem Topology.closure_inter_interior_subset_inter_closures
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    closure (A ∩ interior B) ⊆ closure A ∩ closure B := by
  -- `interior B` is contained in `B`.
  have h₁ : (A ∩ interior B : Set X) ⊆ A ∩ B := by
    intro x hx
    exact ⟨hx.1, interior_subset hx.2⟩
  -- Taking closures preserves inclusions.
  have h₂ : closure (A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h₁
  -- Use the existing lemma for the intersection.
  have h₃ : closure (A ∩ B) ⊆ closure A ∩ closure B :=
    Topology.closure_inter_subset (A := A) (B := B)
  -- Chain the inclusions.
  exact subset_trans h₂ h₃


theorem Topology.interior_closure_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `x` lies in the interior of `closure A`
  have hxA : x ∈ interior (closure A) := by
    -- First, enlarge `closure (A ∩ B)` to `closure A`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    -- Then, pass to interiors
    have h₂ : interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) :=
      interior_mono h₁
    exact h₂ hx
  -- `x` lies in the interior of `closure B`
  have hxB : x ∈ interior (closure B) := by
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    have h₂ : interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB
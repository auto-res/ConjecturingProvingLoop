

theorem Topology.closure_interior_closure_inter_subset_inter_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B : Set X))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- Membership in `closure (interior (closure A))`
  have hxA : x ∈ closure (interior (closure A)) := by
    -- `closure (A ∩ B) ⊆ closure A`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    -- Hence, by monotonicity, `interior (closure (A ∩ B)) ⊆ interior (closure A)`.
    have h₂ :
        (interior (closure (A ∩ B : Set X)) : Set X) ⊆
          interior (closure A) :=
      interior_mono h₁
    -- Taking closures preserves the inclusion.
    have h₃ :
        closure (interior (closure (A ∩ B : Set X))) ⊆
          closure (interior (closure A)) :=
      closure_mono h₂
    exact h₃ hx
  -- Membership in `closure (interior (closure B))`
  have hxB : x ∈ closure (interior (closure B)) := by
    -- `closure (A ∩ B) ⊆ closure B`
    have h₁ : (closure (A ∩ B : Set X)) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    -- Monotone behaviour of `interior`.
    have h₂ :
        (interior (closure (A ∩ B : Set X)) : Set X) ⊆
          interior (closure B) :=
      interior_mono h₁
    -- Take closures to finish.
    have h₃ :
        closure (interior (closure (A ∩ B : Set X))) ⊆
          closure (interior (closure B)) :=
      closure_mono h₂
    exact h₃ hx
  exact And.intro hxA hxB
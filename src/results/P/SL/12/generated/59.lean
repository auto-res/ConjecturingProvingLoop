

theorem Topology.interior_closure_interior_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hxA : x ∈ interior (closure (interior A)) := by
    -- `A ∩ B ⊆ A`
    have h₁ : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    -- `interior (A ∩ B) ⊆ interior A`
    have h₂ : (interior (A ∩ B : Set X) : Set X) ⊆ interior A :=
      interior_mono h₁
    -- `closure (interior (A ∩ B)) ⊆ closure (interior A)`
    have h₃ : closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h₂
    -- Taking interiors yields the desired inclusion
    have h₄ :
        interior (closure (interior (A ∩ B : Set X))) ⊆
          interior (closure (interior A)) :=
      interior_mono h₃
    exact h₄ hx
  have hxB : x ∈ interior (closure (interior B)) := by
    -- `A ∩ B ⊆ B`
    have h₁ : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    -- `interior (A ∩ B) ⊆ interior B`
    have h₂ : (interior (A ∩ B : Set X) : Set X) ⊆ interior B :=
      interior_mono h₁
    -- `closure (interior (A ∩ B)) ⊆ closure (interior B)`
    have h₃ : closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h₂
    -- Taking interiors yields the desired inclusion
    have h₄ :
        interior (closure (interior (A ∩ B : Set X))) ⊆
          interior (closure (interior B)) :=
      interior_mono h₃
    exact h₄ hx
  exact And.intro hxA hxB
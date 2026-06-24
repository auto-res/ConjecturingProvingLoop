

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have h₁ : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  have h₂ : interior (closure (interior (A : Set X))) ⊆ interior (closure A) :=
    interior_mono h₁
  exact Set.Subset.trans hP2 h₂

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → P3 A := by
  intro hAopen
  exact interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hAopen

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hP2A hP2B
  dsimp [P2] at hP2A hP2B ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
      -- `interior A ⊆ interior (A ∪ B)`
      have hIntA_subset : interior A ⊆ interior (A ∪ B) := by
        have h_subset : interior A ⊆ (A ∪ B) := by
          intro z hz
          have hzA : z ∈ A := interior_subset hz
          exact Or.inl hzA
        exact interior_maximal h_subset isOpen_interior
      -- Now lift the inclusion through `closure` and `interior`
      have h_inner_subset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono hIntA_subset)
      exact h_inner_subset hx_in
  | inr hxB =>
      -- `x ∈ B`
      have hx_in : x ∈ interior (closure (interior B)) := hP2B hxB
      -- `interior B ⊆ interior (A ∪ B)`
      have hIntB_subset : interior B ⊆ interior (A ∪ B) := by
        have h_subset : interior B ⊆ (A ∪ B) := by
          intro z hz
          have hzB : z ∈ B := interior_subset hz
          exact Or.inr hzB
        exact interior_maximal h_subset isOpen_interior
      -- Lift the inclusion
      have h_inner_subset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono (closure_mono hIntB_subset)
      exact h_inner_subset hx_in
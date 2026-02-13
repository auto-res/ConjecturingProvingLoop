

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have h1 : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono hcl
  exact Set.Subset.trans hP2 h1

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∪ B) := by
  intro hA hB
  -- We need to show `(A ∪ B) ⊆ interior (closure (interior (A ∪ B)))`
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx' : x ∈ interior (closure (interior A)) := hA hxA
      -- `interior (closure (interior A)) ⊆ interior (closure (interior (A ∪ B)))`
      have hmono : interior (closure (interior A)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior A ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_left)
        have h₂ : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hmono hx'
  | inr hxB =>
      -- `x ∈ B`
      have hx' : x ∈ interior (closure (interior B)) := hB hxB
      -- `interior (closure (interior B)) ⊆ interior (closure (interior (A ∪ B)))`
      have hmono : interior (closure (interior B)) ⊆
          interior (closure (interior (A ∪ B))) := by
        have h₁ : interior B ⊆ interior (A ∪ B) :=
          interior_mono (Set.subset_union_right)
        have h₂ : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h₁
        exact interior_mono h₂
      exact hmono hx'

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior A) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (interior_mono (subset_closure : interior A ⊆ closure (interior A)))
  simpa [interior_interior] using hsubset hx
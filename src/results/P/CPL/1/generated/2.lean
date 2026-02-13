

theorem P1_univ {X : Type*} [TopologicalSpace X] : P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem closure_interior_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure (interior A) = closure A := by
  simpa using closure_interior_eq_of_P1 (A := A) (P1_of_P2 (A := A) h)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hx_closureA : x ∈ closure (interior A) := hA hxA
      have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono h_sub
        exact closure_mono h_int_subset
      exact h_subset hx_closureA
  | inr hxB =>
      -- `x ∈ B`
      have hx_closureB : x ∈ closure (interior B) := hB hxB
      have h_subset : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) := by
        have h_int_subset : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have h_sub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono h_sub
        exact closure_mono h_int_subset
      exact h_subset hx_closureB
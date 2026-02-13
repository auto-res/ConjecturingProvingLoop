

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  exact subset_trans h interior_subset

theorem P2_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P2 A) (hB : P2 B) : P2 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hAx =>
      have hxA : x ∈ interior (closure (interior A)) := hA hAx
      have h_subset :
          (interior (closure (interior A)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (by
                simpa using
                  (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))))
      exact h_subset hxA
  | inr hBx =>
      have hxB : x ∈ interior (closure (interior B)) := hB hBx
      have h_subset :
          (interior (closure (interior B)) : Set X) ⊆
            interior (closure (interior (A ∪ B))) :=
        interior_mono
          (closure_mono
            (interior_mono
              (by
                simpa using
                  (Set.subset_union_right : (B : Set X) ⊆ A ∪ B))))
      exact h_subset hxB

theorem P3_open {X : Type*} [TopologicalSpace X] {A : Set X} (h_open : IsOpen A) : P3 A := by
  intro x hx
  have hx_int : x ∈ interior A := by
    simpa [h_open.interior_eq] using hx
  have h_subset : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact h_subset hx_int

theorem closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : closure A = closure (interior A) := by
  -- We prove the two inclusions separately and deduce equality.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ closure (interior A)`
    have h₁ : (closure A : Set X) ⊆ closure (interior (closure (interior A))) :=
      closure_mono h
    have h₂ :
        (closure (interior (closure (interior A))) : Set X) ⊆
          closure (closure (interior A)) :=
      closure_mono (interior_subset : interior (closure (interior A)) ⊆ closure (interior A))
    intro x hx
    have hx₁ := h₁ hx
    have hx₂ := h₂ hx₁
    simpa [closure_closure] using hx₂
  · -- `closure (interior A) ⊆ closure A`
    exact closure_mono (interior_subset : interior A ⊆ A)

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx
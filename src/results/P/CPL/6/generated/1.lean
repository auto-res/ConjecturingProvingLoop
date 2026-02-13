

theorem P1_empty : P1 (∅ : Set X) := by
  intro x hx
  exact False.elim hx

theorem P2_empty : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P3_univ : P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, interior_univ] using hx

theorem P1_of_open {A : Set X} (hA : IsOpen A) : P1 A := by
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx' : x ∈ closure (interior A) := hP1A hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact hsubset hx'
  | inr hxB =>
      have hx' : x ∈ closure (interior B) := hP1B hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact hsubset hx'

theorem closure_eq_closure_interior_of_P2 {A : Set X} (h : P2 A) : closure A = closure (interior A) := by
  apply le_antisymm
  ·
    have hA : (A : Set X) ⊆ closure (interior A) := by
      intro x hxA
      have hx' : x ∈ interior (closure (interior A)) := h hxA
      exact interior_subset hx'
    have hclosure : closure A ⊆ closure (closure (interior A)) := closure_mono hA
    simpa [closure_closure] using hclosure
  ·
    exact closure_mono interior_subset
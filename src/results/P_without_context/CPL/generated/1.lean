

theorem P2_implies_P1 {A : Set X} : P2 A → P1 A := by
  intro hP2
  intro x hx
  exact interior_subset (hP2 hx)

theorem open_set_P2 {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  have hInt : interior A = A := hA.interior_eq
  have hsubs : (A : Set X) ⊆ interior (closure A) := interior_maximal subset_closure hA
  have : x ∈ interior (closure A) := hsubs hx
  simpa [hInt] using this

theorem open_set_P3 {A : Set X} (hA : IsOpen A) : P3 A := interior_maximal subset_closure hA

theorem P1_union {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hxA_closure : x ∈ closure (interior A) := hP1A hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inl hy
      exact h_subset hxA_closure
  | inr hxB =>
      -- `x` comes from `B`
      have hxB_closure : x ∈ closure (interior B) := hP1B hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_subset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        apply interior_mono
        intro y hy
        exact Or.inr hy
      exact h_subset hxB_closure

theorem P2_empty : P2 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_iff_closure_eq {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)`
      have hA : (A : Set X) ⊆ closure (interior A) := hP1
      have h : closure A ⊆ closure (closure (interior A)) := closure_mono hA
      simpa [closure_closure] using h
  · intro hEq
    intro x hx
    have : (x : X) ∈ closure A := subset_closure hx
    simpa [hEq] using this
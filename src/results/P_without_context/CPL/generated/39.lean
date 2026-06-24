

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` comes from `A`
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- `interior A` is contained in `interior (A ∪ B)`
      have h_subset : interior A ⊆ interior (A ∪ B) := by
        have hA_sub : (A : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inl hy
        exact interior_mono hA_sub
      -- hence the closures enjoy the same monotonicity
      have h_closure_mono : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_mono hx_closure
  | inr hxB =>
      -- `x` comes from `B`
      have hx_closure : x ∈ closure (interior B) := hB hxB
      -- `interior B` is contained in `interior (A ∪ B)`
      have h_subset : interior B ⊆ interior (A ∪ B) := by
        have hB_sub : (B : Set X) ⊆ A ∪ B := by
          intro y hy
          exact Or.inr hy
        exact interior_mono hB_sub
      -- hence the closures enjoy the same monotonicity
      have h_closure_mono : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono h_subset
      exact h_closure_mono hx_closure

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- `x` belongs to the interior of `A` since `A` is open
  have hx_int : x ∈ interior A := by
    simpa [hA.interior_eq] using hx
  -- `interior (interior A)` is contained in `interior (closure (interior A))`
  have hsubset : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono subset_closure
  -- cast `hx_int` to an element of `interior (interior A)` and conclude
  have hx_int_int : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx_int
  exact hsubset hx_int_int

theorem P1_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = A) : P1 A := by
  intro x hx
  simpa [h] using (subset_closure hx)
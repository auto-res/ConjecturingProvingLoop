

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (h : P2 A) : P1 A := by
  intro x hx
  exact interior_subset (h hx)

theorem P2_open_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- Since `A` is open, its interior equals itself
  have hInt : interior A = A := hA.interior_eq
  -- Thus `x ∈ interior A`
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  -- `interior A` is contained in `closure (interior A)`,
  -- hence its interior is contained in `interior (closure (interior A))`
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    -- use monotonicity of `interior`
    have : interior (interior A) ⊆ interior (closure (interior A)) := by
      apply interior_mono
      exact subset_closure
    simpa [hInt] using this
  -- conclude
  exact hsubset hx_int

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure A = Set.univ) : P3 A := by
  intro x hx
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA] using interior_univ
  simpa [h_int] using (Set.mem_univ x)

theorem P3_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P3 A) (hB : P3 B) : P3 (A ∪ B) := by
  intro x hx
  -- useful inclusions
  have hsubsetA : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
    interior_mono
      (closure_mono
        (by
          intro y hy
          exact Or.inl hy))
  have hsubsetB : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
    interior_mono
      (closure_mono
        (by
          intro y hy
          exact Or.inr hy))
  -- case analysis on membership of `x`
  cases hx with
  | inl hxA =>
      exact hsubsetA (hA hxA)
  | inr hxB =>
      exact hsubsetB (hB hxB)
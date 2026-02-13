

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hx
  -- `A` is open, so its interior is itself
  have hInt : interior A = A := hA.interior_eq
  -- hence `x ∈ interior A`
  have hx_int : x ∈ interior A := by
    simpa [hInt] using hx
  -- `interior A` is an open subset of `closure (interior A)`,
  -- so it is contained in the interior of this closure
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  exact h_subset hx_int

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  intro x hx
  have hP2 : P2 A := P2_of_open hA
  have hInt : interior A = A := hA.interior_eq
  have : x ∈ interior (closure (interior A)) := hP2 hx
  simpa [hInt] using this

theorem P2_subset_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P1 A := by
  intro hP2
  exact fun x hx => interior_subset (hP2 hx)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hP1A hP1B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_closure : x ∈ closure (interior A) := hP1A hxA
      have hsubset : interior A ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inl hy)
      exact (closure_mono hsubset) hx_closure
  | inr hxB =>
      have hx_closure : x ∈ closure (interior B) := hP1B hxB
      have hsubset : interior B ⊆ interior (A ∪ B) :=
        interior_mono (by
          intro y hy
          exact Or.inr hy)
      exact (closure_mono hsubset) hx_closure

theorem P1_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `closure (interior A)` and is open,
  -- hence it is contained in the interior of that closure
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · exact subset_closure
    · exact isOpen_interior
  -- Taking closures preserves inclusions
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx
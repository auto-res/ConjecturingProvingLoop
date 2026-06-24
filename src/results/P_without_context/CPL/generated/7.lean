

theorem P2_of_open {X : Type*} [TopologicalSpace X] (A : Set X) (hA : IsOpen A) : P2 (X:=X) A := by
  dsimp [P2]
  intro x hx
  -- `A` is open, hence `interior A = A`
  have hInt : interior A = A := hA.interior_eq
  -- An open set is contained in the interior of any set that contains it
  have hsubset : (A : Set X) ⊆ interior (closure A) :=
    interior_maximal subset_closure hA
  have : x ∈ interior (closure A) := hsubset hx
  simpa [hInt] using this

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] (A : Set X) (h : P2 (X:=X) A) : P1 (X:=X) A := by
  dsimp [P1, P2] at *
  intro x hx
  have h' : x ∈ interior (closure (interior A)) := h hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) h'

theorem P1_iff_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) : P1 (X:=X) A ↔ closure (interior A) = closure A := by
  dsimp [P1]
  constructor
  · intro hP1
    apply subset_antisymm
    · exact closure_mono (interior_subset : interior A ⊆ A)
    · exact closure_minimal hP1 isClosed_closure
  · intro h_eq
    have hsub : (A : Set X) ⊆ closure A := subset_closure
    simpa [h_eq] using hsub

theorem P3_union {X : Type*} [TopologicalSpace X] (A B : Set X) (hA : P3 (X:=X) A) (hB : P3 (X:=X) B) : P3 (X:=X) (A ∪ B) := by
  dsimp [P3] at *
  intro x hx
  cases hx with
  | inl hxA =>
      have hxInt : x ∈ interior (closure A) := hA hxA
      have hIncl : interior (closure A) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (by
          intro y hy
          exact Or.inl hy))
      exact hIncl hxInt
  | inr hxB =>
      have hxInt : x ∈ interior (closure B) := hB hxB
      have hIncl : interior (closure B) ⊆ interior (closure (A ∪ B)) :=
        interior_mono (closure_mono (by
          intro y hy
          exact Or.inr hy))
      exact hIncl hxInt
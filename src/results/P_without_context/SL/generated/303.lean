

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : P2 (X := X) A) : P3 (X := X) A := by
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hA hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact hsubset hx'
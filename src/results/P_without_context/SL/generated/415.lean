

theorem P2_imp_P1_and_P3 {A : Set X} (hA : P2 A) : P1 A ∧ P3 A := by
  unfold P1 P2 P3 at *
  constructor
  · intro x hx
    have hmem : x ∈ interior (closure (interior A)) := hA hx
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    exact hsubset hmem
  · intro x hx
    have hmem : x ∈ interior (closure (interior A)) := hA hx
    have hclosure : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    have hint : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hclosure
    exact hint hmem
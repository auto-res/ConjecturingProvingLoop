

theorem closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  ext x
  constructor
  · intro hx
    have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    have hmem : x ∈ closure (closure (interior A)) :=
      (closure_mono hsubset) hx
    simpa [closure_closure] using hmem
  · intro hx
    have hsubset₁ : interior A ⊆ closure (interior A) := subset_closure
    have hopen : IsOpen (interior A) := isOpen_interior
    have hsubset₂ : interior A ⊆ interior (closure (interior A)) :=
      interior_maximal hsubset₁ hopen
    exact (closure_mono hsubset₂) hx
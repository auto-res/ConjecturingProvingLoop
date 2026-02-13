

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P3 A := by
  have hInt : interior A = A := hA.interior_eq
  constructor
  · intro _hP1
    intro x hx
    have hx_int : x ∈ interior A := by
      simpa [hInt] using hx
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact hsubset hx_int
  · intro _hP3
    intro x hx
    have hx_int : x ∈ interior A := by
      simpa [hInt] using hx
    exact (subset_closure : interior A ⊆ closure (interior A)) hx_int

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro hP3
    intro x hx
    -- First, show that x ∈ interior A (since A is closed and satisfies P3)
    have hx_int : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- Now use the monotonicity of interior/closure
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
    exact hsubset hx_int

theorem P2_univ {X : Type*} [TopologicalSpace X] : P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx


theorem P3_iff_P2_of_closed {A : Set X} (hA : IsClosed A) : P3 A ↔ P2 A := by
  constructor
  · intro hP3
    -- prove `P2 A` assuming `P3 A`
    unfold P2
    intro x hxA
    -- from `P3` we obtain membership in `interior (closure A)`
    have hx_int_cl : x ∈ interior (closure A) := hP3 hxA
    -- since `A` is closed, `closure A = A`
    have hx_intA : x ∈ interior A := by
      simpa [hA.closure_eq] using hx_int_cl
    -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
      -- `interior A ⊆ closure (interior A)`
      have h_sub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      -- apply `interior_mono` and simplify
      simpa [interior_interior] using interior_mono h_sub
    exact h_subset hx_intA
  · intro hP2
    exact P3_of_P2 hP2

theorem P2_iff_P1_of_dense_interior {A : Set X} (h : Dense (interior A)) : P2 A ↔ P1 A := by
  constructor
  · intro hP2
    exact P1_of_P2 (A := A) hP2
  · intro _hP1
    exact P2_of_dense_interior (X := X) (A := A) h
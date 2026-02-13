

theorem P2_iff_P3_of_dense_interior {X} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 A ↔ P3 A := by
  -- From density we know the closure of `interior A` is the whole space.
  have hClosure : closure (interior A) = (Set.univ : Set X) := h.closure_eq
  constructor
  · intro hP2
    exact P3_of_P2 hP2
  · intro _hP3
    exact P2_of_dense_interior (A := A) hClosure
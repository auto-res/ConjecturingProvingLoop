

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact P2_of_open (X := X) (A := A) hA
  · intro hP2
    exact P2_implies_P1 (X := X) (A := A) hP2

theorem P2_of_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h1 : Topology.P1 A) (h3 : Topology.P3 A) : Topology.P2 A := by
  intro x hx
  -- `P1` gives an equality of closures
  have h_eq : (closure (interior A) : Set X) = closure A :=
    (Topology.P1_iff_dense).1 h1
  -- `P3` yields membership in `interior (closure A)`
  have hx_int : x ∈ interior (closure A) := h3 hx
  -- Rewrite using the equality of closures
  simpa [h_eq] using hx_int
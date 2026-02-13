

theorem P3_inter_interior_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A ∩ interior (closure A)) = A := by
  intro hP3
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxA
    have hxInt : x ∈ interior (closure A) := hP3 hxA
    exact ⟨hxA, hxInt⟩
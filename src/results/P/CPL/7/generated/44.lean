

theorem P2_iff_double_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ A ⊆ interior (interior (closure (interior A))) := by
  -- `interior` is idempotent
  have h_eq :
      interior (interior (closure (interior A))) =
        interior (closure (interior A)) := by
    simp [interior_interior]
  constructor
  · intro hP2 x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    simpa [h_eq] using this
  · intro hSub x hxA
    have : x ∈ interior (interior (closure (interior A))) := hSub hxA
    simpa [h_eq] using this

theorem P1_iff_nhd_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x ∈ A, ∀ U, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty) := by
  classical
  constructor
  · intro hP1 x hxA U hU_open hxU
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    exact ((mem_closure_iff).1 hx_cl) U hU_open hxU
  · intro h x hxA
    have h' : ∀ U, IsOpen U → x ∈ U → (U ∩ interior A).Nonempty := by
      intro U hU_open hxU
      exact h x hxA U hU_open hxU
    exact (mem_closure_iff).2 h'
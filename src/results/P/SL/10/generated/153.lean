

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    have hSub : interior A ⊆ (∅ : Set X) := by
      have : interior A ⊆ closure (interior A) := subset_closure
      simpa [h] using this
    -- A set contained in `∅` is `∅`.
    ext x
    constructor
    · intro hx
      have : x ∈ (∅ : Set X) := hSub hx
      simpa using this
    · intro hx
      cases hx
  · intro h
    calc
      closure (interior A) = closure (∅ : Set X) := by
        simpa [h]
      _ = (∅ : Set X) := by
        simp
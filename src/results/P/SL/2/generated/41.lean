

theorem Topology.P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure (A : Set X)) := by
  constructor
  · intro hP3
    -- From `P3 (closure A)` we get `closure A ⊆ interior (closure (closure A))`,
    -- which, after simplifying, becomes `closure A ⊆ interior (closure A)`.
    have hsubset : (closure (A : Set X)) ⊆ interior (closure (closure (A : Set X))) := hP3
    have hsubset' : (closure (A : Set X)) ⊆ interior (closure (A : Set X)) := by
      simpa [closure_closure] using hsubset
    -- Together with the always-true inclusion `interior (closure A) ⊆ closure A`,
    -- we obtain equality.
    have hEq : interior (closure (A : Set X)) = closure (A : Set X) := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset'
    -- An equality with an open set (`interior (closure A)`) yields openness.
    have : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using this
  · intro hOpen
    -- If `closure A` is open, then its interior is itself, giving `P3`.
    intro x hx
    have hIntEq : interior (closure (A : Set X)) = closure (A : Set X) := by
      simpa using hOpen.interior_eq
    have : x ∈ interior (closure (A : Set X)) := by
      simpa [hIntEq] using hx
    simpa [closure_closure] using this
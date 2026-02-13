

theorem P3_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) ↔ IsOpen (closure A) := by
  constructor
  · intro hP3
    dsimp [Topology.P3] at hP3
    have h₁ : closure (A : Set X) ⊆ interior (closure A) := by
      simpa [closure_closure] using hP3
    have h₂ : interior (closure A) ⊆ closure A := interior_subset
    have hEq : interior (closure A) = closure A := subset_antisymm h₂ h₁
    have hOpenInt : IsOpen (interior (closure A)) := isOpen_interior
    simpa [hEq] using hOpenInt
  · intro hOpen
    dsimp [Topology.P3]
    simpa [closure_closure, hOpen.interior_eq]
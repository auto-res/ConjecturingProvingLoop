

theorem Topology.P3_interior_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) ↔ IsOpen (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  have hP3 : Topology.P3 (interior A) := Topology.P3_interior (A := A)
  exact ⟨fun _ => hOpen, fun _ => hP3⟩


theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have hInt : interior A ⊆ interior B := interior_mono h
  have hClos : closure (interior A) ⊆ closure (interior B) := closure_mono hInt
  exact interior_mono hClos hx
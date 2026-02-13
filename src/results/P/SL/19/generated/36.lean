

theorem Topology.interior_closure_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    interior (closure A) ⊆ interior (closure B) := by
  intro x hx
  have hsubset : closure A ⊆ closure B := closure_mono h
  exact (interior_mono hsubset) hx
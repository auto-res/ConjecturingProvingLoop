

theorem Topology.interior_closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
  intro x hx
  have h_closure_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono (interior_mono hAB)
  exact (interior_mono h_closure_subset) hx
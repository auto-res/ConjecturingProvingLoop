

theorem P2_subset_interior_closure_interior_of_subset {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hP2 : Topology.P2 A) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  have h_mono : interior (closure (interior A)) ⊆ interior (closure (interior B)) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    have h_closure : closure (interior A) ⊆ closure (interior B) := closure_mono h_int
    exact interior_mono h_closure
  exact h_mono hx_int
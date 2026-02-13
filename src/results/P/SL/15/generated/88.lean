

theorem P1_subset_closure_interior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1 : Topology.P1 A) :
    A ⊆ closure (interior B) := by
  intro x hxA
  have hx_cl_intA : x ∈ closure (interior A) := hP1 hxA
  have h_int_subset : interior A ⊆ interior B := interior_mono hAB
  have h_cl_subset : closure (interior A) ⊆ closure (interior B) :=
    closure_mono h_int_subset
  exact h_cl_subset hx_cl_intA